---
doc_id: SHI-INT-2026-0001-A
title: Shirushi Codebase Map & Change Playbook
version: "0.1.0"
status: Draft
created_at: 2026-01-01
---

# Shirushi Codebase Map & Change Playbook

本書はShirushiリポジトリの最新構造（2026-01-01時点）と、主要フロー/変更時の着眼点を短時間で把握できるように整理したものです。doc-gen三パス（事実索引→統合→検証）の結果をドキュメント化しました。

## 1. 目的と対象
- **目的**: 新規参加者・既存メンテナ双方が、CLIとコアロジックの責務境界・副作用・安全装置を参照できる地図を提供する。
- **対象**: `src/` 以下のCLI/コア/パーサ/Dimension/Git/LSP/Plugin層、`.shirushi.yml` 等設定、`docs/doc_index.yaml`。
- **前提**: Node.js 18+、pnpm、Gitリポジトリ状態。content_integrityおよび`forbid_id_change`は既定で有効。

## 2. Codebase Map

| モジュール/ディレクトリ | 主責務 | 代表ファイル |
| --- | --- | --- |
| CLI (`src/cli/`) | Commanderで各コマンドを登録し、共通オプション/ログ初期化を担う | `src/cli/index.ts`, `src/cli/commands/*.ts` |
| コア (`src/core/`) | スキャナ、バリデータ、ID生成、assignトランザクション、インデックス整合性などビジネスロジック | `scanner.ts`, `validator.ts`, `generator.ts`, `assign-transaction.ts`, `index-manager.ts` |
| 設定/Dimension (`src/config/`, `src/dimensions/`) | `.shirushi.yml`のロード/検証とdimension handler登録 | `config/loader.ts`, `config/schema.ts`, `dimensions/index.ts` |
| パーサ (`src/parsers/`) | Markdown front matter/YAML/テンプレート解析とdoc_id抽出 | `parsers/markdown.ts`, `parsers/yaml.ts`, `parsers/template.ts` |
| Git/整合性 (`src/git/`, `src/core/content-validator.ts`, `src/core/source-ref-scanner.ts`) | simple-gitラッパ、doc_id変更検出、content_hash+参照警告 | `git/operations.ts`, `git/change-detector.ts`, `core/content-validator.ts`, `core/source-ref-scanner.ts` |
| LSP (`src/lsp/`) | @see doc_id からのGoTo/Hover/References提供、設定キャッシュ | `lsp/server.ts`, `lsp/handlers/*`, `lsp/utils/pattern-matcher.ts` |
| プラグインAPI (`src/plugins/`) | DocumentSource/IndexStore/ChangeTrackerなど外部統合向け型とガード | `plugins/index.ts`, `plugins/types.ts` |

### 2.1 エントリポイント
- CLI: `src/cli/index.ts` → `registerAssignCommand`等がサブコマンドを接続。`shirushi`実行時に`program.parse(process.argv)`後、引数不足ならhelp表示。
- LSP: `shirushi lsp` → `startLspServer`がstdio接続を開始し、Initialize/Definition/Hover/Referencesを登録。
- npmパッケージ: `package.json` の `bin.shirushi` が `dist/cli/index.js` を指す。ビルド成果物は `tsup` により生成。

### 2.2 主要データと不変条件
- `.shirushi.yml`: `doc_globs`, `id_format`, `dimensions`, `reference_patterns`, `content_integrity`, `checksum`等をZodで検証。placeholder未定義/括弧不整合は読み込みで失敗する。
- `docs/doc_index.yaml`: doc_id uniqueness, path存在, content_hash一致を `validateIndexConsistency` が保証。content_integrity有効時はSHA-256が必須。
- `.shirushi.lock`: assign/rehashが排他制御。既存PID生存時はコマンドをブロックする。
- `content_hash`: `normalizeContentForHashing`(LF統一＋末尾trim)後のSHA-256。lintは不一致時にWARNING/ERROR+参照探索を実行。

## 3. 代表フロー

### 3.1 `shirushi lint --base <ref> --check-references`
1. Git環境検証（`validateGitEnvironment`）でリポジトリ/参照整合を確認。
2. `.shirushi.yml`読込→`scanDocuments`がdoc_globs対象を並列パース。preserveContentは`content_integrity.enabled`に追従。
3. `collectDocumentIssues`でdoc_id検証、`validateIndexConsistency`でインデックス差異、`validateContentIntegrity`でcontent_hash不一致を抽出。
4. `createChangeDetector`が`--base`差分からdoc_id改変リストを生成（チェックサム除外ロジック含む）。
5. `scanDocumentReferences + validateReferences`がdoc_id変更対象を参照する文書を`STALE_REFERENCE`で報告。
6. Quiet/table/json出力。エラーが1件でもあれば終了コード1。

### 3.2 `shirushi assign [-n]`
1. （dry-runでなければ）`.shirushi.lock`を取得し、`.shirushi.yml`と`docs/doc_index.yaml`をロード。
2. `scanDocuments`でdoc_id未設定の文書を抽出し、`generateDocId`→`validateDocId`で各doc_idを確定。
3. `prepareChange`が対象ファイルの元内容とkindを保存。dry-run時は書き込みせずプレビュー。
4. `applyChanges`でfront matter/YAMLにdoc_idを書込み、失敗時は`rollback`が原状復帰。
5. `applyIndexUpdate`でインデックスに追記（pathはPOSIX正規化）。引き続き失敗すればロールバック。
6. 結果をtable/jsonで表示し、assigned/skipped/errorsサマリを出力。

### 3.3 `shirushi lsp`
1. `startLspServer`が設定をlazyロードし、TextDocuments経由で@see doc_idを検索。
2. Definition: `findDocIdAtPosition`でdoc_id抽出→`lookupDocument`でindex参照→該当Markdown/YAMLファイルURIを返却。
3. Hover/Referencesも同様にdoc_id→index→ファイルメタデータを返し、content_integrityの警告と連携可能。

## 4. 変更ガイド

### 4.1 id_format / dimension / checksum
- `config/schema.ts`でplaceholder検証 + checksum重複禁止を必ず更新する。
- `generator.ts`/`validator.ts`/`checksum-validator.ts`の3点セットで新dimensionの生成・検証・stripロジックを同期。
- 移行時は `docs/doc_index.yaml` の既存doc_id/serial整合を保持するために `shirushi assign --dry-run`で影響を確認し、`stripChecksumFromDocId` を活用して`forbid_id_change`比較を安全にする。

### 4.2 Parser/Scanner拡張
- MarkdownとYAML両方で`MISSING_ID`や`MULTIPLE_IDS_IN_DOCUMENT`等を維持すること。front matter安全性のため`assertYamlSafety`フローを崩さない。
- `scanDocuments`はfast-glob結果に filterPaths を適用できる前提で`--changed-only`最適化を行うため、API互換を守る。
- UI上の期待出力を壊さないよう、変更後は`shirushi scan --format json`・`shirushi lint --quiet`で差異を確認。

### 4.3 content_integrity / rehash / source references
- `validateContentIntegrity`はcontent_hash未設定をWARNING、ハッシュ不一致をERROR+doc_id収集として扱う。ロジック変更時は `rehash`コマンドとの互換を意識。
- `source_ref-scanner`はReDoS軽減のため`MAX_PATTERN_LENGTH`/`MAX_LINE_LENGTH`を設けている。patternを追加/変更する際はコスト評価を行う。
- `rehash`はdry-runでhash差分が分かるので、content_integrity仕様変更の検証に利用する。

### 4.4 assignトランザクションとロック
- `.shirushi.lock`のレース条件を避けるため、ロックファイル破損時は削除して再作成する仕様を維持。
- `rollback`は書き込み済みファイルを逆順で復元し、index新規作成時は削除する。例外経路を増やす場合は失敗時の`failedPaths`報告を確実にする。
- 変更後は`shirushi assign`をdry-run/実書き込み両方で検証し、`docs/doc_index.yaml`のcontent_hashを`rehash`で更新する。

## 5. 検証とフォローアップ
- このドキュメントは`doc-gen`ワークフロー出力をもとに手動整形した。差分検証は `pnpm test && pnpm lint && pnpm typecheck` で行うことを推奨。
- 追加した知見を `docs/doc_index.yaml` と content_hash に反映させるため、文書更新後は `shirushi rehash` を推奨する。
- 未実装事項: READMEで触れられている `shirushi index sync` は将来の予定。仕様策定時は本書のフロー/インタラクションを参照しつつ追記すること。
