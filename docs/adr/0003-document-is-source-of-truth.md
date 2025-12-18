---
doc_id: SHI-ADR-2025-0003-H
title: "ADR-0003: Document is Source of Truth for doc_id"
version: "1.0.0"
status: Accepted
created_at: 2025-01-19
---

# ADR-0003: Document is Source of Truth for doc_id

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: architecture, data-integrity, index

---

## Context

Shirushi manages two sources of `doc_id` information:

1. **Document files** (Markdown/YAML): Contains `doc_id` in front matter or root
2. **Index file** (`docs/doc_index.yaml`): Central registry of all documents

When these two sources disagree, we need to decide which one takes precedence. This decision affects:

- How we handle conflicts
- What error messages we show
- Update/sync workflows
- User mental model

The specification states:
> **doc 側の `doc_id` を真とする。**
> インデックスが doc の `doc_id` と食い違っている場合、`DOC_ID_MISMATCH_WITH_INDEX` エラーとしてインデックス側の不整合とみなす。

## Decision

**Documents are the source of truth for `doc_id`.**

When validating:
1. Extract `doc_id` from document file
2. Compare with index entry (if exists)
3. If mismatch: Report as `DOC_ID_MISMATCH_WITH_INDEX` error
4. The error indicates the **index is wrong**, not the document

The index file is treated as a **derived artifact** that must be kept in sync with documents.

## Rationale

### Why Document > Index?

1. **Locality**: The `doc_id` is physically present where it's most relevant
2. **Version Control**: Git tracks document changes directly
3. **User Workflow**: Authors edit documents, not the index
4. **Single Source**: Prevents conflicting updates
5. **Tool Independence**: Documents are valid without the index

### Workflow Implications

```
User edits doc → doc_id changes → Index becomes stale → User runs sync command
```

Not:
```
User edits index → Index updates → Document becomes stale
```

## Alternatives Considered

### 1. Index is Source of Truth

Document `doc_id` must match index entry.

**Pros**:
- Central registry approach
- Easier to query all documents
- Could prevent duplicate IDs earlier

**Cons**:
- Users must update two places (document + index)
- Confusing when document shows one ID but index says another
- Index could get out of sync with Git history
- Breaks "edit document, commit" workflow

**Rejected**: Violates principle of locality and single source of truth.

### 2. Both Must Match (No Precedence)

Treat mismatches as symmetric errors.

**Pros**:
- Strict consistency enforcement
- No ambiguity

**Cons**:
- Doesn't help users understand which to fix
- No clear recovery path
- Doesn't align with natural workflow

**Rejected**: Users need clear guidance on resolution.

### 3. Last Modified Wins

Compare file modification times and use the newer one.

**Pros**:
- Automatic conflict resolution
- Works with concurrent edits

**Cons**:
- File times are unreliable (Git checkout, etc.)
- Hidden behavior (users don't understand why one wins)
- Could silently use wrong value
- Doesn't work well with version control

**Rejected**: Too magical, error-prone.

## Consequences

### Positive

- **Clear Mental Model**: Users know documents are authoritative
- **Git-Friendly**: Document history in Git is the true history
- **Simple Workflow**: Edit document, sync index
- **Error Clarity**: "Index is out of sync" is actionable
- **Tool Agnostic**: Other tools can read documents without index

### Negative

- **Index Staleness**: Index can become stale easily
- **Duplicate Detection**: Can't rely solely on index to prevent duplicates
- **Sync Required**: Users must remember to sync index after document changes

### Neutral

- Requires a `shirushi index sync` command (planned)
- CI should validate index consistency

## Implementation Notes

### Validation Logic

```typescript
function validateDocumentAgainstIndex(
  doc: Document,
  indexEntry: IndexEntry | undefined
): ValidationResult {
  if (!indexEntry) {
    return {
      error: 'UNINDEXED_DOC_ID',
      message: `Document ${doc.path} has doc_id ${doc.doc_id} but is not in index`
    };
  }

  if (doc.doc_id !== indexEntry.doc_id) {
    return {
      error: 'DOC_ID_MISMATCH_WITH_INDEX',
      message: `Document ${doc.path} has doc_id ${doc.doc_id}, but index says ${indexEntry.doc_id}. Index is out of sync.`,
      // Note: Error message makes clear that INDEX needs updating
    };
  }

  return { valid: true };
}
```

### Sync Command Behavior

```typescript
// Future: shirushi index sync
function syncIndex(documents: Document[]): void {
  const newIndex = documents.map(doc => ({
    doc_id: doc.doc_id,        // From document (source of truth)
    path: doc.path,
    title: doc.metadata.title,
    // ... other metadata from document
  }));

  writeIndexFile(newIndex);
}
```

### Error Message Example

```
ERROR: DOC_ID_MISMATCH_WITH_INDEX

File: docs/pce/boundary.md
Document doc_id: PCE-SPEC-2025-0001-G
Index doc_id:    PCE-SPEC-2025-0999-X

The index file is out of sync with the document.
To fix: Run `shirushi index sync` to update the index.
```

## Related Decisions

- ADR-0007: Manual Index Synchronization Only (builds on this decision)

## Notes

This decision aligns with the "single source of truth" principle common in software architecture. It's similar to how:

- Code is the source of truth (not documentation)
- Database is the source of truth (not cache)
- Git history is the source of truth (not deployment logs)

The index is essentially a **cache** or **materialized view** of document metadata.
