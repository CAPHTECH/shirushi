# Shirushi 仕様書

バージョン: 0.1.0  
ステータス: Draft  
作成日: 2025-11-19  

---

## 1. 概要

**Shirushi** は、Git リポジトリ内で管理される Markdown / YAML 等のドキュメントに対して、

- 一貫した形式の **ドキュメント ID（`doc_id`）** を付番し、
- ID の欠落・重複・改変を検出し、
- CI（継続的インテグレーション）のゲートとして機能する

ための **ID 管理・検証システム** である。

既存のドキュメント・コード検索 MCP（例: KIRI）が「検索・参照」を担うのに対し、  
Shirushi は「ID とインデックスの整合性・不変性」を担う。

実体としては、設定ファイル `.shirushi.yml` とインデックスファイル `docs/doc_index.yaml` を前提とした CLI ツール `shirushi` である。

---

## 2. 目的と非目的

### 2.1 目的

1. **ID の一貫性と不変性の担保**

   - すべての対象ドキュメントに `doc_id` を付与し、  
     形式・一意性・インデックスとの整合性を保証する。

2. **AI / 人間編集による「勝手な ID 変更」の検出**

   - LLM 等が本文編集時に `doc_id` を書き換えたり削除した場合に、  
     CI で確実に検出しブロックする。

3. **ID 付番とインデックス管理の標準化**

   - リポジトリ内に **インデックスファイル** を持ち、  
     `doc_id ↔ path ↔ メタ情報` を一元管理する。

4. **ツールチェーンとの統合のしやすさ**

   - CLI 形式で提供し、`pre-commit` や CI（GitHub Actions 等）から容易に呼び出せる。
   - `scan` の JSON 出力などを通じて、他ツール（検索、MCP、ダッシュボード等）からも利用可能。

### 2.2 非目的

- ドキュメント内容の品質チェック（文章校正・リンク切れ検出など）は対象外。
- ドキュメント本文の自動生成・自動編集は行わない。
- 高度な承認フロー／レビュー・ワークフローの管理は行わない。

---

## 3. 用語定義

- **ドキュメント (document)**  
  Shirushi の対象とするファイル。現バージョンでは Markdown (`.md`) および YAML (`.yaml` / `.yml`) を対象とする。

- **`doc_id`**  
  ドキュメントに付与される不変の識別子。  
  Shirushi が検証・管理する主対象であり、各ドキュメントにつき **ちょうど 1 つ** 存在しなければならない。

- **インデックスファイル (index file)**  
  ドキュメントの一覧とメタ情報を保持する YAML ファイル。  
  デフォルトパスは `docs/doc_index.yaml`。  
  Shirushi が「ID に紐づく付帯情報の表」として参照する。

- **既存ドキュメント**  
  `shirushi lint --base <ref>` 実行時において、 `<ref>` 時点の Git リビジョンに存在しているドキュメント。

- **新規ドキュメント**  
  `shirushi lint --base <ref>` 実行時において、 `<ref>` には存在せず、現在の HEAD にのみ存在するドキュメント。

---

## 4. ID モデルと DSL

Shirushi における `doc_id` は、次の 2 要素から構成される。

1. **フォーマットテンプレート (`id_format`)**
2. **各パーツの定義 (`dimensions`)**

### 4.1 `id_format`: プレースホルダ文字列

`.shirushi.yml` では、ID のフォーマットを次のように宣言する。

```yaml
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"
```

#### 4.1.1 プレースホルダ名

- プレースホルダは `{NAME}` という形で記述する。
- `NAME` は `[A-Z0-9_]+` の正規表現にマッチする識別子とする。
- `{` と `}` 以外の部分はすべて **リテラル文字列** として扱う（例: `-` など）。

#### 4.1.2 正規表現（id_pattern）の導出

- ツール実装は `id_format` と `dimensions` の定義から、`doc_id` をパースするための正規表現を **自動導出** する。
- ユーザが別途 `id_pattern` を記述する必要はない。
- 各 `{NAME}` 部分は、対応する `dimensions[NAME]` の型情報に基づいて適切なサブパターン（例: `[A-Z]{2,8}`、`[0-9]{4}` 等）へ展開される。

### 4.2 `dimensions`: パーツごとの定義

`dimensions` では、`id_format` 内の各プレースホルダに対応する部品型とルールを宣言する。

```yaml
dimensions:
  COMP: { ... }
  KIND: { ... }
  YEAR4: { ... }
  SER4: { ... }
  CHK1: { ... }
```

現バージョンの Shirushi が標準サポートする部品型は以下の通り。

1. `enum`
2. `enum_from_doc_type`
3. `year`
4. `serial`
5. `checksum`

今後の拡張として、新たな部品型を追加する余地を残す。

---

## 5. 部品型の仕様

### 5.1 `enum`

#### 概要

固定された候補集合から値をとる部品。  
例: `COMP`（コンポーネント名）など。

#### 設定例

```yaml
COMP:
  type: enum
  values: ["PCE", "KKS", "EDGE"]
  select:
    by_path:
      - pattern: "docs/pce/**"
        value: "PCE"
      - pattern: "docs/kakusill/**"
        value: "KKS"
      - pattern: "docs/edge/**"
        value: "EDGE"
```

#### 仕様

- `values`: この部品が取りうる文字列の列挙。
- `select.by_path`（任意）:
  - `pattern`: リポジトリルートからの相対パスに対する **グロブパターン**。
    - 少なくとも `*`, `?`, `**`（ディレクトリ再帰）をサポートする POSIX 風グロブとする。
  - `value`: そのパターンにマッチしたドキュメントに対して期待される `COMP` の値。
  - **評価順序**: 上から順に評価し、最初にマッチしたものを採用する。
- `lint` 時には次を検証する。
  1. `doc_id` 内で観測された値が `values` に含まれていること。
  2. `select.by_path` がある場合、マッチしたルールの `value` と `doc_id` 内の値が一致していること。

---

### 5.2 `enum_from_doc_type`

#### 概要

ドキュメントの `doc_type` フィールドから派生する enum。  
例: `KIND`（ドキュメント種別コード）。

#### 設定例

```yaml
KIND:
  type: enum_from_doc_type
  mapping:
    spec: "SPEC"
    design: "DES"
    memo: "MEMO"
    runbook: "RUN"
    decision: "ADR"
```

#### 仕様

- `mapping`: `doc_type` → `KIND` コードへのマッピング。
- `lint` 時には次を検証する。
  1. ドキュメントのメタデータに `doc_type` が存在すること（必要な場合）。
  2. `doc_type` が `mapping` に含まれていること。
  3. 期待されるコード（`mapping[doc_type]`）と、`doc_id` 中から抽出した `KIND` の値が一致していること。

---

### 5.3 `year`

#### 概要

通常は 4 桁の年を表す部品。  
例: `YEAR4`。

#### 設定例

```yaml
YEAR4:
  type: year
  digits: 4
  source: "created_at"  # または "now"
```

#### 仕様

- `digits`: 年を表す桁数（一般には 4）。
- `source`:
  - `"created_at"`: ドキュメントの作成日メタデータ（存在する場合）を優先。
  - `"now"`: assign 実行時点の現在年を使用。
- `lint` 時には、少なくとも「数字であり、指定された桁数であること」を検証する。

---

### 5.4 `serial`

#### 概要

特定のスコープ内で一意な連番を表す部品。  
例: `SER4`。

#### 設定例

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]
```

#### 仕様

- `digits`: シリアル値の桁数（ゼロパディング）。
- `scope`: 連番のカウンタを分ける単位となる他部品のリスト。
  - 上記例では、「COMP + KIND + YEAR4 ごとに 0001–9999 を採番」する。
- `assign` 時にはインデックスファイルを参照し、同じ `scope` の既存最大値 + 1 を採番する。
- `lint` 時には少なくとも次を検証する。
  1. 桁数が `digits` に一致していること。
  2. インデックス上で `doc_id` が一意であること（重複禁止）。

連番の飛び（0001, 0005, 0100…）まで厳密に検査するかどうかは初期仕様では規定せず、実装や運用ポリシーに委ねる。

---

### 5.5 `checksum`

#### 概要

他の複数部品の値から計算されたチェックサム文字。  
例: `CHK1`。

#### 設定例

```yaml
CHK1:
  type: checksum
  algo: "mod26AZ"
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

#### 仕様

- `algo`:
  - 現バージョンでは最低限 `"mod26AZ"` をサポートする。
    - 対象文字列を適当な方式で数値列に変換し、合計値を 26 で割った余りを A–Z に対応させるシンプルな方式。
- `of`:
  - チェックサム計算の対象となる部品名の配列（順序も含めて定義）。

`lint` 時には次を検証する。

1. `id_format` および `dimensions` に従って部品を抽出。
2. `of` に列挙された部品を連結し、`algo` でチェックサムを再計算。
3. 再計算結果と `doc_id` 中のチェックサム部分が一致していること。

不一致の場合は `INVALID_ID_CHECKSUM` エラーとなる。

---

## 6. 設定ファイル `.shirushi.yml`

### 6.1 例（PCE / Kakusill / EdgePatch を想定）

```yaml
# .shirushi.yml

doc_globs:
  - "docs/**/*.md"
  - "docs/**/*.yaml"
  - "docs/**/*.yml"

id_field: "doc_id"
index_file: "docs/doc_index.yaml"

# ID = COMP-KIND-YEAR4-SER4-CHK1
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"

dimensions:
  COMP:
    type: enum
    values: ["PCE", "KKS", "EDGE"]
    select:
      by_path:
        - pattern: "docs/pce/**"
          value: "PCE"
        - pattern: "docs/kakusill/**"
          value: "KKS"
        - pattern: "docs/edge/**"
          value: "EDGE"

  KIND:
    type: enum_from_doc_type
    mapping:
      spec: "SPEC"
      design: "DES"
      memo: "MEMO"
      runbook: "RUN"
      decision: "ADR"

  YEAR4:
    type: year
    digits: 4
    source: "created_at"

  SER4:
    type: serial
    digits: 4
    scope: ["COMP", "KIND", "YEAR4"]

  CHK1:
    type: checksum
    algo: "mod26AZ"
    of: ["COMP", "KIND", "YEAR4", "SER4"]

forbid_id_change: true
allow_missing_id_in_new_files: false

rules:
  - when:
      doc_type: "spec"
    require_fields:
      - "version"
      - "owner"
```

---

## 7. ドキュメント形式

### 7.1 Markdown ドキュメント

Markdown ファイルは、先頭に YAML front matter を持ち、その中に `doc_id` フィールドを必須とする。

#### 7.1.1 front matter の構造

- ファイル先頭行が `---` の場合、
  - 先頭の `---` から、次に現れる `---` 行までを YAML としてパースする。
- その YAML オブジェクトに `doc_id` フィールドが **ちょうど 1 つ** 存在しなければならない。
- オプションとして `status` および `superseded_by` フィールドを持つことができる。
  - `status`: `Draft`, `Active`, `Deprecated`, `Superseded` のいずれか。
  - `superseded_by`: `status: Superseded` の場合、後継となるドキュメントの `doc_id`。

#### 7.1.2 例

```markdown
---
doc_id: PCE-SPEC-2025-0001-G
title: 境界の定義
doc_type: spec
status: active
version: "1.0.0"
owner: caph/pce
tags:
  - PCE
  - boundary
---

# 境界の定義

...
```

複数の `doc_id` フィールドが存在する場合は `MULTIPLE_IDS_IN_DOCUMENT` エラーとする。

### 7.2 YAML ドキュメント

YAML ファイル（仕様書・原則定義・設定など）は、ルート直下に `doc_id` を必須とする。

#### 7.2.1 例

```yaml
doc_id: KKS-SPEC-2025-0002-F
title: Kakusill サービス原則
doc_type: spec
status: draft
version: "0.3.2"
owner: caph/kakusill
tags:
  - Kakusill
  - principle

principles:
  - ...
```

- ファイルを YAML としてパースしたルートオブジェクトに `doc_id` が存在しない場合は `MISSING_ID` エラー。
- 複数箇所への `doc_id` 記述も `MULTIPLE_IDS_IN_DOCUMENT` として扱う。

---

## 8. インデックスファイル仕様

### 8.1 位置と形式

デフォルトのインデックスファイルはリポジトリルートからの相対パスで以下とする。

```text
docs/doc_index.yaml
```

形式は YAML とし、トップレベルに `documents` キーを持つ。

#### 8.1.1 例

```yaml
# docs/doc_index.yaml

documents:
  - doc_id: PCE-SPEC-2025-0001-G
    path: docs/pce/boundary.md
    title: 境界の定義
    doc_type: spec
    status: active
    version: "1.0.0"
    owner: caph/pce
    tags:
      - PCE
      - boundary

  - doc_id: KKS-SPEC-2025-0002-F
    path: docs/kakusill/service_principles.yaml
    title: Kakusill サービス原則
    doc_type: spec
    status: draft
    version: "0.3.2"
    owner: caph/kakusill
    tags:
      - Kakusill
      - principle
```

### 8.2 制約

- `documents[].doc_id` は全体で一意でなければならない。
- `documents[].path` はリポジトリルートからの相対パスとする。
- `documents[].path` に対応するファイルは実在しなければならない。
- 各ドキュメントファイル側に存在する `doc_id` は、インデックス内の `doc_id` と一致していなければならない。

### 8.3 優先される真実

- **doc 側の `doc_id` を真とする。**
- インデックスが doc の `doc_id` と食い違っている場合、`DOC_ID_MISMATCH_WITH_INDEX` エラーとしてインデックス側の不整合とみなす。

---

## 9. CLI 仕様

CLI コマンド名: `shirushi`  

共通事項:

- カレントディレクトリから `.shirushi.yml` を探索し、設定を読み込む。
- エラー発生時には非 0 の終了コードで終了する。
- `--config <path>` オプションで設定ファイルを明示指定できる実装を推奨する。

### 9.1 `shirushi lint`

ドキュメントとインデックスの整合性を検証する。

```bash
shirushi lint [--base <git-ref>] [--changed-only]
```

#### 9.1.1 挙動

1. `.shirushi.yml` を読み込み、`doc_globs` に基づいて対象ドキュメントを列挙。
2. 各ドキュメントから `doc_id` を抽出。
3. `id_format` と `dimensions` から導出された正規表現で `doc_id` をパースし、部品ごとに分解。
4. 各 `dimensions[NAME]` の型に応じた検査を行う（enum/mapping/year/serial/checksum など）。
5. インデックスファイルを読み込み、`doc_id` ↔ `path` の整合性を検査。
6. `--base <git-ref>` が指定されている場合:
   - `<git-ref>` 時点の対象ファイルを取得。
   - 既存ドキュメントについて、`doc_id` が変更されていないか検査。
   - このとき初めて「新規ドキュメント」の概念が生じる。
7. 1つでも致命的エラーがあれば終了コード 1 とする。

#### 9.1.2 Git との関係

- `--base` オプションが **指定されていない** 場合:
  - Git リポジトリの存在は前提とせず、全対象ファイルを「同一の世代」とみなす。
  - `allow_missing_id_in_new_files` は考慮されず、`doc_id` が欠落していればエラー。

- `--base <git-ref>` が **指定されている** 場合:
  - Git リポジトリであることが前提。
  - `<git-ref>` と HEAD の差分を用いて「既存」「新規」を判定する。
  - 実装によっては、`allow_missing_id_in_new_files = true` の場合、新規ファイルの `MISSING_ID` を警告扱いにダウングレードするなどのポリシーを設定可能。

---

### 9.2 `shirushi scan`

ドキュメントをスキャンし、`doc_id` とメタ情報の一覧を出力する。

```bash
shirushi scan [--format table|json|yaml]
```

- `--format table`（デフォルト）:
  - 人間が読みやすい表形式で標準出力に表示。
- `--format json` / `yaml`:
  - 他ツールやスクリプトから消費しやすい形式で出力。

出力項目の例:

- `doc_id`
- `path`
- `title`
- `doc_type`
- `status`
- `version`
- `owner`

---

### 9.3 `shirushi assign`（将来実装）

`doc_id` 未設定のドキュメントに対して、新しい ID を発番し埋め込む。

```bash
shirushi assign [--dry-run]
```

想定される挙動:

1. `doc_globs` に基づいて対象ドキュメントを列挙。
2. `doc_id` を持たないドキュメントに対して:
   - `id_format` と `dimensions` に基づき、部品を左から順に決定していく。
   - `enum` / `enum_from_doc_type` / `year` / `serial` / `checksum` などのルールに従って値を決定。
3. 生成した `doc_id` をドキュメントに書き込み（front matter / YAML ルート）、インデックスに追記。
4. `--dry-run` の場合はファイルを書き換えず、予定される変更内容を出力する。

---

## 10. エラーコード

Shirushi は `shirushi lint` 実行時に、代表的なエラーコードを用いて問題を報告する。

- `MISSING_ID`  
  - 対象ドキュメントに `doc_id` が存在しない。
  - `allow_missing_id_in_new_files: true` の場合、新規ファイル（`--base` との差分で検出）についてはこのエラーは除外される。

- `MULTIPLE_IDS_IN_DOCUMENT`  
  - 1 つのドキュメント内に複数の `doc_id` フィールドが存在する。

- `INVALID_ID_FORMAT`  
  - `doc_id` が `id_format` および `dimensions` から導出された正規表現にマッチしない。

- `INVALID_ID_CHECKSUM`  
  - `checksum` 部品の再計算結果が `doc_id` 中の値と一致しない。

- `INVALID_ENUM_VALUE`  
  - `enum` / `enum_from_doc_type` 型部品の値が許容されていない（`values` や `mapping` に存在しない）。

- `ENUM_SELECTION_MISMATCH`  
  - 例えば `select.by_path` で期待される `COMP` と、実際の `doc_id` 中の `COMP` が一致しない。

- `MISSING_FILE_FOR_INDEX`  
  - インデックスファイル上には存在するが、対応するファイルが存在しない。

- `UNINDEXED_DOC_ID`  
  - ドキュメント内に `doc_id` が存在するが、インデックスに対応エントリが存在しない。

- `DOC_ID_MISMATCH_WITH_INDEX`  
  - インデックスの `doc_id` とドキュメント側 `doc_id` が一致しない。

- `DOC_ID_CHANGED`  
  - `--base <git-ref>` 実行時に、既存ドキュメントの `doc_id` が `<git-ref>` 時点から変更されている。

致命的エラー（デフォルトで CI を fail させるべきもの）と  
警告レベル（運用によりブロックしない選択もありうるもの）の仕分けは、実装および組織のポリシーに委ねる。

---

## 11. CI 統合（参考）

### 11.1 GitHub Actions の例

```yaml
name: Shirushi DocID Lint

on:
  pull_request:
    paths:
      - "docs/**"
      - ".shirushi.yml"

jobs:
  docid-lint:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0  # base ブランチとの差分を取得するため

      - uses: actions/setup-node@v4
        with:
          node-version: "22"

      - run: pnpm install
      - run: pnpm shirushi:lint -- --base origin/${{ github.base_ref }}
```

`package.json`:

```json
{
  "scripts": {
    "shirushi:lint": "shirushi lint"
  }
}
```

---

## 12. 将来の拡張

- 新たな部品型（例: `env`・`region`・`regex` 型など）の追加。
- `status` の状態遷移ルール（`draft → active → deprecated/superseded`）の形式化と lint への組み込み。
- `superseded_by: <doc_id>` のような関係性情報の導入。
- `shirushi` 自体を MCP として提供し、エージェントや IDE プラグインから利用できる API として公開。
- 複数インデックスファイルのサポート（サブツリーごとの index 等）。
- 他形式（JSON, TOML, AsciiDoc など）への対応。

---

以上が Shirushi v0.1 の仕様である。
