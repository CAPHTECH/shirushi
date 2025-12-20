---
doc_id: SHI-ADR-2025-0009-N
title: "ADR-0009: Separate Checksum from doc_id"
version: "1.0.0"
status: Accepted
created_at: 2025-12-20
---

# ADR-0009: Separate Checksum from doc_id

**Status**: Accepted

**Date**: 2025-12-20

**Deciders**: Architecture Team

**Tags**: checksum, doc_id, traceability, breaking-change

---

## Context

Issue #14 identified a fundamental design problem: including the checksum as part of `doc_id` creates a traceability conflict.

### Current Design

```yaml
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"
# Example: PCE-SPEC-2025-0001-G
```

The complete `doc_id` (including checksum) is used for:
- Document identification
- Index file keys
- External references
- `forbid_id_change` validation

### The Problem

| Scenario | What Happens | Impact |
|----------|--------------|--------|
| Checksum corruption | `INVALID_ID_CHECKSUM` + `DOC_ID_CHANGED` errors | Cannot recover without "changing" ID |
| Checksum correction | `forbid_id_change` blocks the fix | Deadlock: error detected but unfixable |
| External reference | References break when checksum changes | Traceability lost |

### Design Contradiction

ADR-0004 states:

> The checksum is **not** for: Security (preventing malicious tampering)
> The checksum **is** for: Catching accidental typos

If the checksum is for **detection**, it should not be part of the immutable identifier. Detection implies the ability to **correct** what was detected.

## Decision

**Separate the checksum from `doc_id` into its own field.**

### New Document Format

```yaml
---
doc_id: PCE-SPEC-2025-0001
checksum: G
title: Boundary Definition
---
```

### New Configuration

```yaml
# .shirushi.yml
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}"

dimensions:
  COMP: { type: enum, values: ["PCE", "BACK", "GW"] }
  KIND: { type: enum_from_doc_type, ... }
  YEAR4: { type: year, digits: 4 }
  SER4: { type: serial, digits: 4, scope: ["COMP", "KIND", "YEAR4"] }

# Checksum configuration (separate from id_format)
checksum:
  field: "checksum"       # Field name in document metadata
  algo: "mod26AZ"
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

### New Index Format

```yaml
documents:
  - doc_id: PCE-SPEC-2025-0001
    checksum: G
    path: docs/pce/boundary.md
    title: Boundary Definition
```

### Behavioral Changes

| Aspect | Before | After |
|--------|--------|-------|
| `forbid_id_change` target | Full ID with checksum | `doc_id` only (no checksum) |
| Checksum mismatch | `INVALID_ID_CHECKSUM` (error) | `INVALID_CHECKSUM` (error, fixable) |
| `rehash` command | Recalculates content hash | Also recalculates checksum |
| External references | Match full ID | Match `doc_id` only |

## Alternatives Considered

### Alternative A: Checksum as Verification-Only (Canonical ID vs Display ID)

```
Canonical ID: PCE-SPEC-2025-0001     (for index, references)
Display ID:   PCE-SPEC-2025-0001-G   (for human readability)
```

**Pros:**
- Keeps checksum visible in documents
- Less breaking change to document format

**Cons:**
- Two ID concepts create ambiguity
- "Which ID do I write in the document?" is unclear
- Implementation complexity for maintaining two views

**Rejected:** Conceptual ambiguity outweighs benefits.

### Alternative B: Immutable Checksum with --force Flag

Keep current design but add `--force` flag to allow checksum corrections.

**Pros:**
- Minimal implementation change
- Backwards compatible

**Cons:**
- Contradicts ADR-0004's purpose ("detection" that can't be corrected)
- `--force` is a workaround, not a solution
- Doesn't solve external reference stability

**Rejected:** Does not address the fundamental design flaw.

## Consequences

### Positive

- **Conceptual clarity**: Identifier and verification are separate concerns
- **ADR-0004 alignment**: Checksum is purely for detection (and correction)
- **Stable references**: External systems can rely on `doc_id` without checksum volatility
- **Fixable errors**: `INVALID_CHECKSUM` can be corrected without "changing" the ID
- **Single Responsibility**: `doc_id` identifies, `checksum` verifies

### Negative

- **Breaking change**: All existing documents require migration
- **Configuration change**: `id_format` must be updated
- **Index migration**: Index file structure changes
- **Documentation update**: User guide, examples need revision

### Neutral

- Checksum validation logic remains the same (mod26AZ algorithm unchanged)
- `assign` command needs adjustment but logic is similar
- ADR-0004 remains valid for the algorithm; this ADR complements it

## Migration Plan

### Phase 1: Deprecation Warning (v0.3)
- Add warning when checksum is detected in `id_format`
- Support both old and new formats during transition
- Add `shirushi migrate` command to assist migration

### Phase 2: New Format Default (v0.4)
- New projects use separated checksum by default
- Old format still supported with deprecation warning

### Phase 3: Legacy Removal (v1.0)
- Remove support for checksum in `id_format`
- Require explicit `checksum` configuration block

## Related Decisions

- **ADR-0004**: Simple mod26AZ Checksum Algorithm (complemented, not superseded)
- **ADR-0003**: Document is Source of Truth (unchanged)
- **Issue #14**: Checksum Traceability Problem (resolved)

## Notes

This is a **breaking change** but addresses a fundamental design flaw. The migration path allows gradual adoption while maintaining backwards compatibility during transition.

References:
- [Issue #14: Checksum Traceability Problem](https://github.com/CAPHTECH/shirushi/issues/14)
- Similar patterns: Git (commit hash vs GPG signature), npm (version vs integrity hash)
