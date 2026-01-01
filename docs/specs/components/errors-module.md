---
title: Error Definitions Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: errors-definitions
artifacts:
  - constants: LawDomain, ErrorSeverity
    usage: categorize config/parser/validation/git/system domains
    evidence: src/errors/definitions.ts:1
  - record: ShirushiErrors
    entries:
      - Parser domain (MISSING_ID, INVALID_FRONT_MATTER, ...)
      - Validation domain (INVALID_ID_FORMAT, DOC_ID_MISMATCH_WITH_INDEX, ...)
      - Git domain (DOC_ID_CHANGED, NOT_A_GIT_REPO, ...)
      - Assign/Content integrity domains
    evidence: src/errors/definitions.ts:32
  - type: ShirushiErrorCode = keyof typeof ShirushiErrors
    evidence: src/errors/definitions.ts:199
integration_points:
  - CLI reporters reference codes for coloring/severity
  - Validators/dimension handlers emit codes for LDE tracing
```

# 層B: 振る舞いspec
```yaml
behavior:
  invariants:
    - statement: "Every error definition includes code/message/domain/severity"
      confidence: Observed
      evidence: src/errors/definitions.ts:32
    - statement: "Domains partition errors into Config/Parser/Validation/Git/System"
      confidence: Observed
      evidence: src/errors/definitions.ts:1
  postconditions:
    - statement: "Downstream modules import ErrorSeverity, LawDomain enums for consistent reporting"
      confidence: Observed
      evidence: src/cli/output/reporters.ts:10
  side_effects: none
```

# 層C: 業務意味spec（草案）
Error定義モジュールは、ShirushiのLaw Driven Engineeringでいう「違反語彙」の台帳であり、CLI/サービスログ/正式証跡の整合性を取るための単一情報源となっている。各コードがSeverityやDomainを含むことで、CIの失敗分類や監査ログの集計が容易になる。Git/Assign/Content-integrityといった横断ドメインのエラーもここで体系化され、formal model（TLA+/Alloy）とのトレーサビリティが維持される。

> NOTE: 草案です。新たなLawを追加する際はエラーコードのメンテも忘れずに。
```
