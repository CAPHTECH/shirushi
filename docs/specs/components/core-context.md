---
title: Core Context (Planned) Component Spec
generated_at: 2026-01-01
status: draft
---

> NOTE: 内部設計書で定義されている `core/context.ts` は現在リポジトリに実装ファイルが存在しない（2026-01-01 時点）。以下は docs/api/internal-design.md の記述をAs-Isとして整理したものであり、実装追加時のベースラインとする。

# 層A: インターフェースspec（設計書由来）
```yaml
component: core-context (planned)
responsibility: "Assemble ShirushiConfig, document snapshots, index data, git facade, logger into a CoreContext"
structures:
  - CoreContext:
      config: ShirushiConfig
      documents: DocumentSnapshot[]
      index: IndexFile
      git: GitFacade
      logger: Logger
    evidence: docs/api/internal-design.md:31
```

# 層B: 振る舞いspec（設計書由来）
```yaml
behavior:
  flows:
    - name: lint
      description: CoreContextBuilder loads config, enumerates documents, attaches git diff snapshots before validator.run
      confidence: Observed (design)
      evidence: docs/api/internal-design.md:50
    - name: assign
      description: builder prepares context and feeds generator with documents lacking IDs
      evidence: docs/api/internal-design.md:63
```

# 層C: 業務意味spec（草案）
CoreContextはCLIとコアアルゴリズムの橋渡しをするコンテナ層として設計されている。構成要素を一括提供することで、validator/generator/scan等のモジュールから副作用や依存解決を切り離し、formalモデルと整合する進行状態を維持することが狙い。未実装のため、実装時にはこのspecを満たすよう構築が必要である。
```
