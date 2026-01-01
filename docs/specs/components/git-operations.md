---
title: Git Operations Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: git-operations
public_api:
  - class: SimpleGitOperations
    methods:
      - isGitRepository(): Either<GitError, boolean>
        evidence: src/git/operations.ts:65
      - isValidRef(ref): Either<GitError, boolean>
        evidence: src/git/operations.ts:82
      - getFileContent(path, ref?)
        description: Read from working tree or git show ref:path, returns string|null
        evidence: src/git/operations.ts:94
      - getChangedFiles(baseRef?)
        description: Return ChangedFile[] via diff --name-status or git status
        evidence: src/git/operations.ts:135
    dependencies: simple-git library, ShirushiErrors
  - factory: createGitOperations(config)
    returns: SimpleGitOperations instance
    evidence: src/git/operations.ts:205
helpers:
  - parseDiffNameStatus(output) -> ChangedFile[]
  - statusToChangedFiles(status) -> ChangedFile[]
error_model:
  - GitError includes code, message, context (ref/path)
    evidence: src/git/operations.ts:26
```

# 層B: 振る舞いspec
```yaml
behavior:
  preconditions:
    - statement: "Git commands require repository context; non-repo returns right(false) for isGitRepository"
      confidence: Observed
      evidence: src/git/operations.ts:68
  postconditions:
    - statement: "getFileContent returns null (Right) when file missing rather than throwing"
      confidence: Observed
      evidence: src/git/operations.ts:98
    - statement: "Changed file detection preserves rename info (oldPath)"
      confidence: Observed
      evidence: src/git/operations.ts:185
  side_effects:
    - type: git_cli_invocation
      detail: "Uses simple-git wrappers to run rev-parse/diff/status"
      confidence: Observed
      evidence: src/git/operations.ts:12
  invariants:
    - statement: "All GitErrors created via createGitError include original message for traceability"
      confidence: Observed
      evidence: src/git/operations.ts:26
```

# 層C: 業務意味spec（草案）
Git Operationsはforbid_id_changeやchanged-only lintといった監査モードのデータ源であり、doc_id変更検出や参照整合性チェックの前提となる。simple-git越しに安全なEitherエラーモデルを採用することで、Git障害がValidationエラーとして報告され、改ざん/欠落リスクを早期に表面化できる。renameサポートやworking tree読み込みは、ドキュメントID監視を開発フローに密接させるための設計意図である。

> NOTE: 業務意味層は草案です。Git運用ポリシー変更時は spec を更新してください。
```
