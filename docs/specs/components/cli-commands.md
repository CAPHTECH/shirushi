---
title: CLI Commands Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: cli-commands
commands:
  - name: lint
    description: "Validate doc_id structure, index consistency, content hashes, git diffs, and reference integrity"
    options:
      - flag: "--format <table|json>"
      - flag: "--quiet"
      - flag: "--base <ref>"
      - flag: "--changed-only"
      - flag: "--check-references"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - scanDocuments()
      - validateIndexConsistency()
      - validateContentIntegrity()
      - createChangeDetector().detectDocIdChanges()
      - scanDocumentReferences()/validateReferences()
      - scanSourceReferences()/filterReferencesByDocIds()
    confidence: Observed
    evidence:
      - src/cli/commands/lint.ts:1
      - src/cli/commands/lint.ts:336
      - src/cli/commands/lint.ts:404
      - src/cli/commands/lint.ts:421
      - src/cli/commands/lint.ts:428
      - src/cli/commands/lint.ts:494
      - src/cli/commands/lint.ts:530
      - src/cli/commands/lint.ts:572
  - name: scan
    description: "Enumerate documents via doc_globs and print doc_id + metadata"
    options:
      - flag: "--format <table|json|yaml>"
      - flag: "--config <path>"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - scanDocuments()
      - toScanOutput()/formatScanResult()
    confidence: Observed
    evidence:
      - src/cli/commands/scan.ts:1
      - src/cli/commands/scan.ts:42
      - src/cli/commands/scan.ts:55
      - src/cli/commands/scan.ts:62
  - name: show
    description: "Lookup an index entry by doc_id and render metadata/content"
    options:
      - flag: "--format <table|json|yaml>"
      - flag: "--json"
      - flag: "--yaml"
      - flag: "--path-only"
      - flag: "--meta-only"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - lookupDocument()
      - formatShowResult()
    confidence: Observed
    evidence:
      - src/cli/commands/show.ts:1
      - src/cli/commands/show.ts:63
      - src/cli/commands/show.ts:78
      - src/cli/commands/show.ts:88
      - src/cli/commands/show.ts:111
  - name: assign
    description: "Generate doc_id values for files lacking IDs and update docs + index"
    options:
      - flag: "--format <table|json>"
      - flag: "--dry-run"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - acquireLock()/releaseLock()
      - loadIndexFile()
      - scanDocuments(preserveContent)
      - generateDocId()
      - prepareChange()/applyChanges()/rollback()
    confidence: Observed
    evidence:
      - src/cli/commands/assign.ts:1
      - src/cli/commands/assign.ts:93
      - src/cli/commands/assign.ts:102
      - src/cli/commands/assign.ts:137
      - src/cli/commands/assign.ts:150
      - src/cli/commands/assign.ts:195
  - name: rehash
    description: "Recompute content_hash for each indexed document and persist"
    options:
      - flag: "--format <table|json>"
      - flag: "--dry-run"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - acquireLock()/releaseLock()
      - loadIndexFile()
      - scanDocuments(preserveContent: true)
      - calculateContentHash()
    confidence: Observed
    evidence:
      - src/cli/commands/rehash.ts:1
      - src/cli/commands/rehash.ts:81
      - src/cli/commands/rehash.ts:124
      - src/cli/commands/rehash.ts:130
      - src/cli/commands/rehash.ts:152
      - src/cli/commands/rehash.ts:170
  - name: lsp
    description: "Start Shirushi LSP server (stdio) for doc_id navigation"
    options:
      - flag: "--config <path>"
    exit_codes:
      success: process never returns (server)
      failure: non-zero via thrown error
    calls:
      - startLspServer()
    confidence: Observed
    evidence:
      - src/cli/commands/lsp.ts:1
      - src/cli/commands/lsp.ts:45
      - src/cli/commands/lsp.ts:50
  - name: skill (install/list/uninstall)
    description: "Manage OpenSkills-compatible skill bundles for AI agents"
    options:
      - flag: "install --target <agent|claude> --global --path --force"
      - flag: "list"
      - flag: "uninstall --target <agent|claude> --global --path"
    exit_codes:
      success: 0
      failure: 1
    calls:
      - resolveSkillPath()/getSkillSourceDir()
      - executeSkillInstall()/executeSkillUninstall()/executeSkillList()
    confidence: Observed
    evidence:
      - src/cli/commands/skill.ts:1
      - src/cli/commands/skill.ts:111
      - src/cli/commands/skill.ts:187
      - src/cli/commands/skill.ts:323
      - src/cli/commands/skill.ts:367
```

# 層B: 振る舞いspec
```yaml
behavior:
  flows:
    - name: lint
      preconditions:
        - statement: "When --base or --changed-only is set, a Git repository with the referenced ref must be accessible"
          confidence: Observed
          evidence: src/cli/commands/lint.ts:342
      postconditions:
        - statement: "Returns exit code 1 if any error or warning of severity error is produced"
          confidence: Observed
          evidence: src/cli/commands/lint.ts:620
      side_effects:
        - type: git_read
          detail: "Reads changed files and file contents via GitOperations"
          confidence: Observed
          evidence: src/cli/commands/lint.ts:367
        - type: filesystem_read
          detail: "Scans doc files and index files via scanDocuments + validateIndex"
          confidence: Observed
          evidence: src/cli/commands/lint.ts:404
        - type: analysis
          detail: "Derives stale reference warnings by scanning all documents when doc_id changes"
          confidence: Observed
          evidence: src/cli/commands/lint.ts:530
    - name: assign
      preconditions:
        - statement: "Non-dry-run execution must hold a filesystem lock to serialize doc/index writes"
          confidence: Observed
          evidence: src/cli/commands/assign.ts:102
        - statement: "Config + index + documents must load successfully before generation proceeds"
          confidence: Observed
          evidence: src/cli/commands/assign.ts:130
      postconditions:
        - statement: "Generates doc_id per template and writes doc/index patches atomically unless dry-run"
          confidence: Observed
          evidence: src/cli/commands/assign.ts:178
      side_effects:
        - type: filesystem_write
          detail: "prepareChange/applyChanges mutate markdown/YAML front matter and index file"
          confidence: Observed
          evidence: src/cli/commands/assign.ts:178
    - name: rehash
      preconditions:
        - statement: "Requires index file to exist; fails fast otherwise"
          confidence: Observed
          evidence: src/cli/commands/rehash.ts:141
      postconditions:
        - statement: "Updates or adds content_hash entries unless dry-run"
          confidence: Observed
          evidence: src/cli/commands/rehash.ts:170
      side_effects:
        - type: filesystem_write
          detail: "Writes updated index entries after hashing when not dry-run"
          confidence: Observed
          evidence: src/cli/commands/rehash.ts:81
    - name: show
      preconditions:
        - statement: "doc_id must exist in index; otherwise command exits with error"
          confidence: Observed
          evidence: src/cli/commands/show.ts:78
      postconditions:
        - statement: "Outputs either full document metadata + optional content, path only, or metadata-only view"
          confidence: Observed
          evidence: src/cli/commands/show.ts:88
    - name: skill
      invariants:
        - statement: "Install/uninstall paths must be under current workspace or home directory"
          confidence: Observed
          evidence: src/cli/commands/skill.ts:111
      side_effects:
        - type: filesystem_write
          detail: "Copies packaged skills directory into resolved installation target"
          confidence: Observed
          evidence: src/cli/commands/skill.ts:187
```

# 層C: 業務意味spec（草案）
CLIコマンド群は、Shirushiのユーザー接点として各責務を分担し、設定読み込み・コンテキスト構築とコアロジック呼び出しを司る（docs/api/internal-design.md:16）。その役割分担は内部設計書のコンポーネント表でも「`cli/commands/*` は引数パースと `CoreContext` 呼び出しに専念」と定義されており、組織的にはIDガバナンスをCLIワークフローに落とし込む位置づけである。lint/scan/show/assign/rehashは品質ゲートやCI統合に直結し、skill/lspはAIやIDEエージェント連携の導線を備えている。これらの行動が正しく評価・監査されることで、ドキュメントIDの不変条件（forbid_id_change等）が人・ツール双方で守られ、証跡つきに管理される。

> NOTE: 業務意味層はドキュメント由来の意図を記述した草案です。コードのみから厳密に導けないため、レビューでの補強を推奨します。
```
