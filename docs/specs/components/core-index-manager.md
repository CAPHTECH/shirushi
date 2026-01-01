---
title: Index Manager Component Spec
generated_at: 2026-01-01
status: draft
---

# 層A: インターフェースspec
```yaml
component: core-index-manager
public_api:
  - function: createIndexEntrySchema(idField?) / createIndexFileSchema(idField?)
    purpose: Build Zod validators for dynamic id_field
    evidence: src/core/index-manager.ts:27
  - function: loadIndexFile(indexPath, cwd?, idField?)
    description: Read YAML with JSON schema, return IndexFile or null
    evidence: src/core/index-manager.ts:108
  - function: validateIndexConsistency(documents, indexFile, cwd?, idField?)
    description: Detect missing files, duplicates, mismatches, return errors + maps
    outputs:
      - errors: LintError[]
      - indexEntries: Map<path, IndexEntry>
      - indexByDocId: Map<docId, IndexEntry>
    evidence: src/core/index-manager.ts:324
  - helper: getDocIdFromEntry(entry, idField)
    description: Safe accessor for dynamic fields
    evidence: src/core/index-manager.ts:99
  - helper: getIndexFilePath(indexFile, cwd?)
    evidence: src/core/index-manager.ts:356
structures:
  - IndexEntry: doc_id?, path, metadata fields, content_hash, arbitrary fields
    evidence: src/core/index-manager.ts:61
  - IndexValidationResult
```

# 層B: 振る舞いspec
```yaml
behavior:
  preconditions:
    - statement: "Index YAML must satisfy dynamically generated schema; otherwise loadIndexFile throws"
      confidence: Observed
      evidence: src/core/index-manager.ts:132
  postconditions:
    - statement: "validateIndexConsistency emits UNINDEXED_DOC_ID when doc_id exists but path missing in index"
      confidence: Observed
      evidence: src/core/index-manager.ts:282
    - statement: "Missing physical files produce MISSING_FILE_FOR_INDEX"
      confidence: Observed
      evidence: src/core/index-manager.ts:188
    - statement: "Duplicate doc_id detection records first/duplicate paths"
      confidence: Observed
      evidence: src/core/index-manager.ts:150
  side_effects:
    - type: filesystem_read
      detail: "existsSync + readFile to inspect docs/doc_index.yaml"
      confidence: Observed
      evidence: src/core/index-manager.ts:14
  invariants:
    - statement: "Paths normalized for cross-platform comparison before map lookup"
      confidence: Observed
      evidence: src/core/index-manager.ts:280
```

# 層C: 業務意味spec（草案）
Index Managerは、文書台帳（doc_index.yaml）と実ファイルの双方向整合性を保障する。CIやlintで参照されるエラーコード（UNINDEXED_DOC_ID, DOC_ID_MISMATCH_WITH_INDEX, DUPLICATE_DOC_ID_IN_INDEX 等）を集中定義し、doc/indexの差異を即座に可視化する役割を持つ。content_hashやowner等の派生メタデータもIndexEntry経由で型安全に扱えるため、将来の監査や差分検出の基盤となる。

> NOTE: 草案につき、indexファイル仕様変更時は併せて更新してください。
```
