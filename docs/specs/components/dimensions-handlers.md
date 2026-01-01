---
title: Dimension Handlers Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: dimensions-handlers
registries:
  - name: DimensionRegistry
    methods:
      - register(type, handler)
      - get(type)
      - has(type)
      - getRegisteredTypes()
    singleton: getDimensionRegistry()
    evidence: src/dimensions/index.ts:30
handlers:
  - type: enum
    file: src/dimensions/handlers/enum.ts
    validate: value ∈ values & select.by_path match
    generate: first matching rule or first value
    toPattern: alternation of escaped values
    evidence:
      - src/dimensions/handlers/enum.ts:33
  - type: enum_from_doc_type
    file: src/dimensions/handlers/enum-from-doc-type.ts
    validate: enforce mapping + doc_type presence
    generate: map doc_type to configured value
    evidence:
      - src/dimensions/handlers/enum-from-doc-type.ts:31
  - type: year
    file: src/dimensions/handlers/year.ts
    validate: digit length + range
    generate: from metadata.created_at or current year
    evidence:
      - src/dimensions/handlers/year.ts:33
  - type: serial
    file: src/dimensions/handlers/serial.ts
    validate: digit length, >0
    generate: scope-aware reservation using indexEntries/template
    evidence:
      - src/dimensions/handlers/serial.ts:119
  - type: checksum
    file: src/dimensions/handlers/checksum.ts
    validate: compute algorithm (mod26AZ) across referenced parts
    generate: recompute from otherParts
    evidence:
      - src/dimensions/handlers/checksum.ts:45
shared_interfaces:
  - DimensionHandler (validate, generate, toPattern)
    evidence: src/dimensions/handlers/base.ts:27
  - ValidationContext / GenerationContext structures
    evidence: src/dimensions/handlers/base.ts:32
```

# 層B: 振る舞いspec
```yaml
behavior:
  invariants:
    - statement: "Handlers return fp-ts Either; Left carries specific ShirushiError codes"
      confidence: Observed
      evidence: src/dimensions/handlers/base.ts:18
    - statement: "Checksum handler enforces uppercase single-letter output"
      confidence: Observed
      evidence: src/dimensions/handlers/checksum.ts:53
  preconditions:
    - statement: "Serial handler requires scope dimension values present in otherParts"
      confidence: Observed
      evidence: src/dimensions/handlers/serial.ts:44
    - statement: "Enum_from_doc_type requires metadata.doc_type"
      confidence: Observed
      evidence: src/dimensions/handlers/enum-from-doc-type.ts:43
  postconditions:
    - statement: "Registry registration executed once via default singleton"
      confidence: Observed
      evidence: src/dimensions/index.ts:47
  side_effects:
    - type: none (pure computations; serial reads indexEntries array)
```

# 層C: 業務意味spec（草案）
Dimension handlers体制は、ShirushiのIDテンプレートDSLを実装面と形式仕様双方で整合させる基盤である。各handlerがLawカード化された制約（例: enum select-by-path、doc_type→KIND対応、serialスコープユニーク）を直接コード化し、fp-ts Eitherで証跡化された違反を返す。Registryシングルトンにより、新しいdimension追加でもCLI/validator/generatorが即時恩恵を受け、formal-syncやAlloy/TLA+モデリングと並走できる構造になっている。

> NOTE: 業務意味層は草案です。Law/Term catalog更新時は本specを併せて見直してください。
```
