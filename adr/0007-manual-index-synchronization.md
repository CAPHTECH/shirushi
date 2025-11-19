# ADR-0007: Manual Index Synchronization Only

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: index, sync, workflow, safety

---

## Context

Shirushi maintains two sources of truth:
1. **Documents** with `doc_id` fields (primary source of truth per ADR-0003)
2. **Index file** (`docs/doc_index.yaml`) with document metadata (derived data)

The index can become stale when:
- Documents are added, removed, or modified
- `doc_id` values change
- Metadata fields are updated

We need to decide: **When and how should the index be synchronized?**

## Decision

**Index synchronization will be manual only** (explicit user action).

The `shirushi lint` command is **read-only** and will:
- ✅ Detect index inconsistencies
- ✅ Report errors (e.g., `UNINDEXED_DOC_ID`, `DOC_ID_MISMATCH_WITH_INDEX`)
- ❌ Never modify the index file
- ❌ Never write to any files

A separate command will handle synchronization (v0.2):
```bash
shirushi index sync [--dry-run]
```

## Rationale

### Why Manual Sync?

1. **Predictability**
   - Users know exactly when files are modified
   - No surprises in CI or during validation
   - Clear separation: validate vs. modify

2. **Safety**
   - Read-only commands can't accidentally corrupt data
   - CI runs are safe (no file modifications)
   - Easier to reason about command behavior

3. **Version Control Hygiene**
   - User decides when to commit index changes
   - Index updates are deliberate, not automatic
   - Git history shows intentional sync operations

4. **Explicit Intent**
   - Syncing is an intentional action
   - User confirms they want to update index
   - Reduces chance of accidental overwrites

5. **CI-Friendly**
   - CI should never modify files
   - Validation commands must be idempotent
   - Read-only operations are parallelizable

## Alternatives Considered

### 1. Auto-Sync on Lint

`shirushi lint` automatically updates index when detecting staleness.

```bash
shirushi lint
# Automatically fixes index if out of sync
```

**Pros**:
- Convenient (one command does everything)
- Always up-to-date index
- Less for users to remember

**Cons**:
- Violates principle of least surprise
- CI runs would modify files (bad practice)
- Can't run validation without side effects
- Harder to debug (did lint find issues or fix them?)
- Breaks Git workflows (uncommitted changes after validation)

**Rejected**: Too magical, violates CI best practices.

### 2. Auto-Sync with `--fix` Flag

`shirushi lint` validates by default, `--fix` updates index.

```bash
shirushi lint           # Read-only validation
shirushi lint --fix     # Validate and fix index
```

**Pros**:
- Clear opt-in to modifications
- Similar to ESLint `--fix` pattern
- Single command with dual mode

**Cons**:
- Still mixes validation and modification
- Flag can be forgotten in CI (accidentally fixes)
- Command has two very different behaviors
- Harder to test (two code paths)

**Rejected**: Prefer separate commands for separate concerns.

### 3. Auto-Sync on Every Document Change

Automatically update index whenever a document is modified.

**Pros**:
- Index always in sync
- No manual step needed
- Can't forget to sync

**Cons**:
- Requires file watching or Git hooks
- Too complex for v0.1
- Intrusive (automatic file modifications)
- What if index write fails?
- Doesn't work in all environments

**Rejected**: Too complex, too much magic.

### 4. No Index File at All

Remove the index file concept entirely.

**Pros**:
- No sync problem (nothing to sync)
- Simpler mental model
- One source of truth

**Cons**:
- Breaks specification requirement
- Can't efficiently query all documents
- Serial number generation becomes harder
- Loses benefits of centralized metadata

**Rejected**: Index is core to the design.

## Consequences

### Positive

- **Clear Separation**: Validation vs. modification are distinct operations
- **Safety**: `lint` can never corrupt data
- **CI-Friendly**: CI runs are read-only and idempotent
- **Predictable**: Users know when files are modified
- **Git-Friendly**: User controls when index changes are committed
- **Testable**: Simpler testing (separate concerns)

### Negative

- **Extra Step**: Users must remember to run sync command
- **Stale Index**: Index can become stale between syncs
- **Documentation**: Must clearly explain two-step workflow

### Neutral

- Common pattern (e.g., `git add` is separate from `git status`)
- Users familiar with two-phase operations

## Workflow Examples

### Typical Workflow

```bash
# 1. User edits a document, changes doc_id
vim docs/pce/boundary.md

# 2. Validate (detects index is stale)
shirushi lint
# ERROR: DOC_ID_MISMATCH_WITH_INDEX
# docs/pce/boundary.md has doc_id PCE-SPEC-2025-0001-G
# but index says PCE-SPEC-2025-0999-X

# 3. Sync index (v0.2 command)
shirushi index sync --dry-run  # Preview changes
shirushi index sync            # Actually update

# 4. Validate again (should pass)
shirushi lint
# ✓ All documents valid

# 5. Commit both document and index
git add docs/pce/boundary.md docs/doc_index.yaml
git commit -m "Update boundary definition ID"
```

### CI Workflow

```yaml
# .github/workflows/shirushi.yml
- name: Validate Document IDs
  run: shirushi lint --base origin/main

# Note: No sync command in CI (read-only)
```

### Error Detection

```bash
shirushi lint

# Output:
ERROR: UNINDEXED_DOC_ID
  File: docs/new-doc.md
  doc_id: PCE-SPEC-2025-0010-X
  This document is not in the index.
  → Run `shirushi index sync` to add it.

ERROR: DOC_ID_MISMATCH_WITH_INDEX
  File: docs/pce/boundary.md
  Document: PCE-SPEC-2025-0001-G
  Index:    PCE-SPEC-2025-0999-X
  → Run `shirushi index sync` to update index.

ERROR: MISSING_FILE_FOR_INDEX
  Index entry: docs/deleted-doc.md (PCE-SPEC-2025-0005-E)
  File not found.
  → Run `shirushi index sync` to remove from index.

❌ 3 errors found. Run `shirushi index sync` to fix.
```

## Implementation Notes

### Lint Command (Read-Only)

```typescript
// src/cli/commands/lint.ts
export async function lintCommand(options: LintOptions): Promise<void> {
  // Read documents
  const documents = await scanDocuments(options);

  // Read index
  const index = await loadIndex(options.indexFile);

  // Validate (READ-ONLY - no writes)
  const errors = validateDocumentsAgainstIndex(documents, index);

  // Report errors
  reportErrors(errors);

  // Exit with appropriate code
  process.exit(errors.length > 0 ? 1 : 0);

  // ❌ NEVER WRITES TO FILES
}
```

### Sync Command (Write) - v0.2

```typescript
// src/cli/commands/index/sync.ts (future)
export async function indexSyncCommand(options: SyncOptions): Promise<void> {
  // Read documents (source of truth)
  const documents = await scanDocuments(options);

  // Build new index from documents
  const newIndex = buildIndexFromDocuments(documents);

  // Show changes (if dry-run)
  if (options.dryRun) {
    showChanges(oldIndex, newIndex);
    return;
  }

  // Write index file
  await writeIndexFile(options.indexFile, newIndex);

  console.log('✓ Index synchronized');
}
```

### Error Messages

Errors should guide users to the sync command:

```typescript
const errorMessages = {
  UNINDEXED_DOC_ID: (file: string, docId: string) => `
    Document ${file} has doc_id ${docId} but is not in index.
    Run 'shirushi index sync' to add it.
  `,

  DOC_ID_MISMATCH_WITH_INDEX: (file: string, docId: string, indexId: string) => `
    Document ${file} has doc_id ${docId}, but index says ${indexId}.
    The index is out of sync.
    Run 'shirushi index sync' to update the index.
  `,

  MISSING_FILE_FOR_INDEX: (file: string, docId: string) => `
    Index references ${file} (${docId}), but file not found.
    Run 'shirushi index sync' to remove from index.
  `,
};
```

## Future Enhancements

### v0.2: Sync Command

```bash
shirushi index sync [options]

Options:
  --dry-run         Show changes without writing
  --index-file      Path to index file (default: docs/doc_index.yaml)
  --force           Overwrite index even if conflicts exist
```

### Future: Auto-Sync Option (v0.3+)

If user demand is high, could add opt-in auto-sync:

```yaml
# .shirushi.yml
index:
  auto_sync: true  # Experimental feature
```

But this would require:
- Clear documentation of risks
- Extensive testing
- Backup/rollback mechanism
- Probably not worth the complexity

## Related Decisions

- ADR-0003: Document is Source of Truth (foundation for this decision)
- ADR-0005: Defer assign Command (similar reasoning about file writes)

## Notes

### Principle: Read-Only Validation

This decision follows a common principle in CLI tools:

- **Validation commands are read-only**: `git status`, `eslint`, `prettier --check`, `shirushi lint`
- **Modification commands are explicit**: `git add`, `eslint --fix`, `prettier --write`, `shirushi index sync`

### Inspiration from Other Tools

| Tool | Validate | Modify |
|------|----------|--------|
| ESLint | `eslint` | `eslint --fix` |
| Prettier | `prettier --check` | `prettier --write` |
| Git | `git status` | `git add` |
| Shirushi | `shirushi lint` | `shirushi index sync` |

This pattern is well-established and users understand it.

### Safety First

When in doubt, prefer safety over convenience. It's easier to add convenience features later than to fix data corruption bugs.
