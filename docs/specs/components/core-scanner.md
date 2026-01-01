---
title: Core Scanner Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: core-scanner
public_api:
  - function: scanDocuments(config, options?)
    description: "Enumerate files via doc_globs, parse markdown/yaml, return documents + summary"
    options:
      - cwd?: string
      - filterPaths?: string[]
      - preserveContent?: boolean
    returns:
      - documents: DocumentParseResult[]
      - summary: ScanSummary
    evidence:
      - src/core/scanner.ts:121
  - function: scanSpecificPaths(paths, config, cwd?, preserveContent?)
    description: "Parse explicit list bypassing glob search"
    evidence: src/core/scanner.ts:202
internal_helpers:
  - getDocumentKind(filePath)
  - parseDocument(filePath, cwd, idField, preserveContent)
structures:
  - ScanSummary fields: totalFiles/markdownFiles/yamlFiles/withDocId/withoutDocId/withProblems
    evidence: src/core/scanner.ts:32
inputs:
  - ShirushiConfig (doc_globs, id_field)
  - Parsers: parseMarkdownFile, parseYamlFile
outputs:
  - DocumentParseResult path-normalized to cwd (relative)
```

# 層B: 振る舞いspec
```yaml
behavior:
  preconditions:
    - statement: "config.doc_globs must match at least zero files; fast-glob handles globs"
      confidence: Observed
      evidence: src/core/scanner.ts:129
  postconditions:
    - statement: "documents include only supported extensions (.md/.yaml/.yml)"
      confidence: Observed
      evidence: src/core/scanner.ts:65
    - statement: "summary counts reflect DocumentParseResult array"
      confidence: Observed
      evidence: src/core/scanner.ts:163
  invariants:
    - statement: "parseDocument returns relative path even if absolute input"
      confidence: Observed
      evidence: src/core/scanner.ts:88
  side_effects:
    - type: filesystem_read
      detail: "Reads doc files; optionally loads content when preserveContent"
      confidence: Observed
      evidence: src/core/scanner.ts:94
```

# 層C: 業務意味spec（草案）
ScannerはShirushiの「観測」フェーズに該当し、doc_globsで定義された情報空間を正規化してCore層へ渡す。doc_idなしの検出やwithProblems集計は、assign/lint/scanといったCLIユースケースで即座にアクションを導く指標となる。preserveContentフラグにより、content_integrityやリファレンス追跡といった後段の観測アルゴリズムが重複読み込みを避けられるよう最適化されている。

> NOTE: 業務意味層は草案であり、BIやCI要件と照合してください。
```
