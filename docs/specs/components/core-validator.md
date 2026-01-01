---
title: Core Validator Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: core-validator
public_api:
  - function: validateDocId(input, config)
    description: "Parse doc_id using template, verify each dimension, return ValidationResult"
    inputs:
      - docId
      - documentPath
      - documentMeta
      - ShirushiConfig (id_format, dimensions)
    outputs:
      - valid: boolean
      - errors: ValidationError[]
      - parsedParts: Record<string,string> when valid
    evidence:
      - src/core/validator.ts:190
  - function: buildIdPattern(config)
    description: "Compile id_format template into RegExp or ValidatorError"
    evidence: src/core/validator.ts:244
  - function: isValidIdFormat(docId, config)
    description: "Boolean shortcut using buildIdPattern"
    evidence: src/core/validator.ts:269
  - function: validateDocuments(inputs[], config)
    description: "Batch wrapper returning Map<path, ValidationResult>"
    evidence: src/core/validator.ts:283
  - function: summarizeResults(resultsMap)
    description: "Aggregate counts and errorsByPath"
    evidence: src/core/validator.ts:304
supporting_types:
  - ValidationResult
  - ValidationInput
  - ValidatorError
  - ClassifiedDimensions (internal)
dependencies:
  - Template parser (parseTemplate / extractDimensionValues)
  - DimensionRegistry handlers
  - ShirushiErrors codes
```

# 層B: 振る舞いspec
```yaml
behavior:
  preconditions:
    - statement: "ShirushiConfig.id_format and dimensions must parse successfully; otherwise errors propagate as MALFORMED/INVALID_TEMPLATE"
      confidence: Observed
      evidence: src/core/validator.ts:195
  postconditions:
    - statement: "If any dimension handler returns ValidationError, validateDocId returns valid=false with aggregated errors"
      confidence: Verified
      evidence: src/core/validator.ts:228
    - statement: "checksum validations execute after non-checksum dimensions"
      confidence: Observed
      evidence: src/core/validator.ts:228
    - statement: "summarizeResults increments valid/invalid counts consistently with Map size"
      confidence: Observed
      evidence: src/core/validator.ts:324
  invariants:
    - statement: "Dimension handlers retrieved via registry must exist; missing handler throws"
      confidence: Observed
      evidence: src/core/validator.ts:132
  side_effects:
    - type: none (pure functions)
```

# 層C: 業務意味spec（草案）
ValidatorはShirushi全体の「doc_idはテンプレートどおりである」保証を担い、エラーをLaw Domainに即して構造化する。Dimension毎の検証結果がLDE（Law Driven Engineering）の証跡としてCLI/CIに伝搬し、ドキュメントID変更や生成ワークフローの品質ゲートとなる。Checksumの遅延評価やバッチ集計機能により、CIでも低コストで全ファイルを審査できる設計になっている。

> NOTE: 業務意味層は草案であり、正式な要件確認を推奨します。
```
