---
doc_id: SHI-FORMAL-2025-0003-H
title: "shirushi formal-sync 仕様"
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# `shirushi formal-sync` 仕様

## 目的
- `.shirushi.yml` に定義された `id_format`・dimension・enum 値を **Alloy/TLA+ の定数** に自動投影し、モデルと実装の乖離を無くす。
- 生成した定数片を formal 検証 (Docker `verify`) の直前に読み込み、構成変更が常に Alloy/TLA+ に反映される状態を維持する。
- placeholder 未定義・enum 不一致などの設定ミスを CI の formal フェーズで即座に検知する。

## CLI インターフェース
```
shirushi formal-sync \
  --config <path|default=.shirushi.yml> \
  --output formal/generated \
  [--check-only] [--verbose]
```

| フラグ | 説明 |
|--------|------|
| `--config` | 読み込む設定ファイルパス (デフォルト: カレントの `.shirushi.yml`) |
| `--output` | 生成物を書き出すディレクトリ (git 無管理)。`formal/generated/` を推奨 |
| `--check-only` | 既存生成物を比較し差分があれば exit code 1。CI キャッシュ用 |
| `--verbose` | Alloy/TLA+ へ書き出した定数 JSON/TLA フラグメントをログ出力 |

## 生成パイプライン
1. **Config 読込**: Zod スキーマで `.shirushi.yml` を検証。`doc_index`/`docs/**/*.md` もスキャンして placeholder 実データを抽出。
2. **共通中間表現 (CIR)**: 以下の JSON を構築。
   ```json
   {
     "placeholders": ["COMP", "KIND", ...],
     "enum": { "COMP": ["PCE", "EDGE", ...] },
     "year": { "YEAR4": { "digits": 4, "values": ["2024", ...] } },
     "serial": { "SER4": { "digits": 4, "scopes": ["COMP", "KIND", "YEAR4"] } },
     "checksum": { "CHK1": { "targets": ["COMP", ...], "algorithm": "mod26AZ" } }
   }
   ```
3. **Alloy 断片生成** (`generated/alloy-constants.als`):
   - `CompUniverse`, `KindUniverse`, `YearUniverse` などの `one sig` を定義。
   - `EnumRule` シーケンスを config の `select.by_path` に合わせて作成。
   - Config と実データにズレがあれば生成を中断し exit code 2。
4. **TLA+ 定数生成** (`generated/tla-constants.tla`):
   - `CompCodes`, `KindCodes`, `YearCodes`, `SerialStrings`, `ScopeKeys` 等を 
     `CONSTANT` 値として書き出す。
   - `EnumSelection`, `KindMapping`, `YearSelection`, `SerialFormatter`, `ScopeKeyBuilder` を CIR から計算。
5. **検証**: 生成結果を以下のルールでチェック。
   - placeholder 完全性: `id_format` に現れるすべてのプレースホルダが CIR に存在する。
   - enum 値一致: `.shirushi.yml` の `values` と `docs/` 実データに現れる値集合が一致。
   - serial スコープ: `scope` に指定された次元が `id_format` に必ず含まれる。
   - check-only の場合は既存ファイルと byte-for-byte 比較。

## CI / Docker 連携
- `formal/docker-compose.yml` の `verify` サービスは `verify-all` 実行前に `shirushi formal-sync --output formal/generated --check-only` を起動する。
- GitHub Actions でも同一ステップを追加し、生成結果を artifact として保存。差分が出た場合は `--check-only` が失敗し、PR へ出力をコメント。
- ローカル開発者は `npm run formal:sync && docker-compose run --rm verify` をワンコマンド化予定 (README 追記済)。

## 失敗時の扱い
| チェック | 例 | 対応 |
|----------|----|------|
| placeholder 不一致 | `id_format` に `{REGION}` があるが config に未定義 | CLI がエラーと差分候補を表示し exit code 3 |
| enum 値欠落 | `.shirushi.yml` の `values` に `EDGE` があるが docs に出現しない | 警告を出しつつ生成は継続 (オプションで厳格化) |
| 生成ファイルを書き換えようとした | `--check-only` でも差分がある | exit code 4 で CI を失敗 |

## 今後の拡張
- `.shirushi.yml` に `dimensions[].handler` を追加し、formal-sync が Alloy/TLA+ の handler predicate を自動有効化できるようにする。
- 生成された TLA+ 定数を `EXTENDS GeneratedConstants` で読み込む構成へ移行し、人手による定数編集を廃止する。
- 生成物のダイジェストを `formal/generated/.checksum` に出力し、CI でキャッシュキーとして利用する。
