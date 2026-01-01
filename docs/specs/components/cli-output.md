---
title: CLI Output Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: cli-output
modules:
  - name: reporters
    responsibilities:
      - "Transform DocumentProblem/ValidationError into human-friendly LintError"
      - "Aggregate issues into table/json summaries"
    apis:
      - function: problemToLintError(path, problem)
        input: DocumentProblem parsed by scanners/validators
        output: LintError DTO
        evidence: src/cli/output/reporters.ts:55
      - function: validationErrorToLintError(path, error, domain?)
        output: LintError with severity=error
        evidence: src/cli/output/reporters.ts:71
      - function: buildLintResult(allIssues)
        output: {errors, warnings, summary}
        evidence: src/cli/output/reporters.ts:230
      - function: formatLintResult(result, format)
        formats: table|json|yaml
        evidence: src/cli/output/reporters.ts:194
      - function: formatLintQuiet(result)
        purpose: machine-friendly list of failing paths
        evidence: src/cli/output/reporters.ts:212
    confidence: Observed
  - name: formatters
    responsibilities:
      - "Convert scan/show outputs into table/json/yaml"
      - "Provide shared helper for CLI commands"
    apis:
      - function: toScanEntry(doc)
        maps DocumentParseResult to view model
        evidence: src/cli/output/formatters.ts:45
      - function: formatScanResult(output, format)
        formats summary counts + rows
        evidence: src/cli/output/formatters.ts:168
      - function: formatShowResult(result, format, mode)
        supports full/meta-only/path-only
        evidence: src/cli/output/formatters.ts:291
      - function: toShowOutput(result, includeContent)
        yields JSON/YAML DTO with typed metadata guards
        evidence: src/cli/output/formatters.ts:225
    confidence: Observed
inputs:
  - LintError, DocumentProblem, ValidationError structures from validators
  - LookupResult/ScanSummary from core modules
outputs:
  - Human-readable console strings (chalk formatting for lint table)
  - JSON/YAML serializations (indent=2)
```

# 層B: 振る舞いspec
```yaml
behavior:
  invariants:
    - statement: "formatters/reporters remain pure and do not mutate inputs"
      confidence: Observed
      evidence: src/cli/output/reporters.ts:71
  side_effects:
    - type: stdout_string
      detail: "Chalk-colored table rows for lint errors/warnings"
      confidence: Observed
      evidence: src/cli/output/reporters.ts:140
    - type: serialization
      detail: "JSON.stringify and js-yaml dump used for machine outputs"
      confidence: Observed
      evidence: src/cli/output/reporters.ts:181
      evidence_alt: src/cli/output/formatters.ts:70
  preconditions:
    - statement: "Callers must supply consistent summary counts when using buildLintResult; function recomputes sets to guard double counting"
      confidence: Observed
      evidence: src/cli/output/reporters.ts:230
  postconditions:
    - statement: "formatScanAsTable always includes total/markdown/yaml counts"
      confidence: Observed
      evidence: src/cli/output/formatters.ts:87
    - statement: "formatShowResult returns path string when mode=path-only regardless of format parameter"
      confidence: Observed
      evidence: src/cli/output/formatters.ts:297
```

# 層C: 業務意味spec（草案）
CLI出力コンポーネントは、品質検証結果をエンジニアやCIログが迅速に解釈できるよう整形する役割を担う。Lint結果では違反サマリーを視認性高く表示しつつ、JSON/YAMLで機械取り込みも可能とすることで、CIステージやbot通知に連携しやすくする意図がある。Scan/show出力は台帳マッピング（doc_index ↔ 実ファイル）の確認作業を定型化し、レビューの再現性を確保する。表現層が純粋関数で構成されているため、将来のUI/daemon連携でも副作用を気にせず再利用できる点が設計判断として現れている。

> NOTE: 業務意味層はコードとドキュメントから推測した草案です。製品要件の確認が必要です。
```
