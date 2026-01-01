---
title: ID Generator Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: core-generator
public_api:
  - function: generateDocId({documentPath, documentMeta, config, indexEntries})
    description: "Parse template, call dimension handlers, output docId + parts"
    returns:
      - Either<GenerationError[], {docId, parts}>
    evidence:
      - src/core/generator.ts:47
      - src/core/generator.ts:67
  - helper: generateParts(template, config, documentPath, documentMeta, indexEntries)
    description: "Compute non-checksum parts first, then checksum dims"
    evidence: src/core/generator.ts:104
  - helper: assembleDocId(templateString, parts)
    description: "Replace placeholders sequentially"
    evidence: src/core/generator.ts:212
inputs:
  - ShirushiConfig.id_format + dimensions definitions
  - DimensionRegistry (handlers support generate)
  - IndexEntry[] for serial scopes
outputs:
  - docId string (As-Is ID)
  - parts map for auditing downstream
error_codes:
  - INVALID_TEMPLATE, UNDEFINED_DIMENSION, DIMENSION_HANDLER_CRASH, SERIAL_OVERFLOW, etc.
```

# 層B: 振る舞いspec
```yaml
behavior:
  preconditions:
    - statement: "config.id_format must parse successfully"
      confidence: Observed
      evidence: src/core/generator.ts:72
    - statement: "Serial dimensions require scope parts + template/index metadata"
      confidence: Observed
      evidence: src/core/generator.ts:132
  postconditions:
    - statement: "Checksum dimensions processed only after all other parts resolved"
      confidence: Observed
      evidence: src/core/generator.ts:176
    - statement: "Errors from handlers accumulate; function returns Left if any"
      confidence: Observed
      evidence: src/core/generator.ts:133
  side_effects:
    - type: none (pure generation)
  invariants:
    - statement: "IndexEntries optional; when absent serial defaults to '0001'"
      confidence: Observed
      evidence: src/core/generator.ts:196
```

# 層C: 業務意味spec（草案）
Generatorはassignフローの心臓部で、Doc IDを構成する各dimensionの由来を明示することで監査可能性を確保している。Serial scopeとChecksum再計算をコードで一貫処理するため、人手によるID付与ミスを排除し、docs/indexの双方向整合性を保つ。partsマップが返る設計は、CLI出力やエビデンスログで「どのdimensionがどの値を採用したか」を可視化する意図による。

> NOTE: 草案のため、ビジネスルールの補強は別途必要です。
```
