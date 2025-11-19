# PCE / Kakusill / EdgePatch Configuration Example

This is the full-featured example from the Shirushi specification, demonstrating a multi-component project setup.

## Project Structure

This example simulates a project with three components:

- **PCE** (Product Catalog Engine) - `docs/pce/`
- **KKS** (Kakusill) - `docs/kakusill/`
- **EDGE** (EdgePatch) - `docs/edge/`

## ID Format

```
{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}
```

**Example IDs**:
- `PCE-SPEC-2025-0001-G` - PCE specification #1 from 2025
- `KKS-SPEC-2025-0002-F` - Kakusill specification #2 from 2025
- `EDGE-ADR-2025-0001-M` - EdgePatch ADR #1 from 2025
- `PCE-DES-2025-0001-K` - PCE design document #1 from 2025

## Dimensions

### COMP (enum with path selection)

Component identifier automatically determined by file path.

**Values**:
- `PCE` - Files in `docs/pce/**`
- `KKS` - Files in `docs/kakusill/**`
- `EDGE` - Files in `docs/edge/**`

**Path Selection**: The component is automatically selected based on where the document is located.

### KIND (enum_from_doc_type)

Document kind derived from the `doc_type` metadata field.

**Mapping**:
- `spec` → `SPEC` (Specification)
- `design` → `DES` (Design Document)
- `memo` → `MEMO` (Memo/Notes)
- `runbook` → `RUN` (Operational Runbook)
- `decision` → `ADR` (Architecture Decision Record)

### YEAR4 (year)

4-digit year from document's `created_at` field.

### SER4 (serial)

4-digit sequential number, scoped by `[COMP, KIND, YEAR4]`.

**Example Scopes**:
- `PCE-SPEC-2025`: 0001, 0002, 0003, ...
- `PCE-DES-2025`: 0001, 0002, 0003, ... (separate counter)
- `KKS-SPEC-2025`: 0001, 0002, 0003, ... (separate counter)

### CHK1 (checksum)

Single character (A-Z) checksum using mod26AZ algorithm.

**Purpose**: Detect accidental ID modifications.

## Document Types

### Specification (spec)

Required fields:
- `version`
- `owner`

Example:
```markdown
---
doc_id: PCE-SPEC-2025-0001-G
title: Boundary Definition
doc_type: spec
status: active
version: "1.0.0"
owner: "caph/pce"
created_at: "2025-01-15"
tags:
  - PCE
  - boundary
---

# Boundary Definition
...
```

### Design Document (design)

Example:
```yaml
doc_id: KKS-DES-2025-0001-H
title: API Design
doc_type: design
status: draft
created_at: "2025-01-16"
owner: "caph/kakusill"

design:
  overview: ...
  endpoints: ...
```

### Architecture Decision Record (decision)

Example:
```markdown
---
doc_id: EDGE-ADR-2025-0001-M
title: Use GraphQL for API
doc_type: decision
status: accepted
created_at: "2025-01-17"
---

# ADR-0001: Use GraphQL for API

## Status
Accepted

## Context
...
```

## Usage

### Validate Documents

```bash
shirushi lint --config examples/pce-kakusill-edge/.shirushi.yml
```

### Scan Documents

```bash
shirushi scan --config examples/pce-kakusill-edge/.shirushi.yml --format table
```

### Compare with Git Base

```bash
shirushi lint --config examples/pce-kakusill-edge/.shirushi.yml --base origin/main
```

## File Organization

```
docs/
├── pce/                    # PCE component documents
│   ├── boundary.md         # doc_id: PCE-SPEC-2025-0001-G
│   └── api-design.yaml     # doc_id: PCE-DES-2025-0001-K
│
├── kakusill/               # Kakusill component documents
│   └── principles.yaml     # doc_id: KKS-SPEC-2025-0002-F
│
├── edge/                   # EdgePatch component documents
│   └── adr/
│       └── 0001-graphql.md # doc_id: EDGE-ADR-2025-0001-M
│
└── doc_index.yaml          # Central index
```

## Validation Features

### Path-Based Component Validation

Documents in `docs/pce/` **must** have `COMP = PCE` in their doc_id.

**Valid**:
```
# File: docs/pce/boundary.md
doc_id: PCE-SPEC-2025-0001-G  ✓
```

**Invalid**:
```
# File: docs/pce/boundary.md
doc_id: KKS-SPEC-2025-0001-G  ✗
# ERROR: ENUM_SELECTION_MISMATCH
# Expected COMP=PCE for path docs/pce/**, got KKS
```

### Checksum Validation

Checksums are automatically validated:

```
doc_id: PCE-SPEC-2025-0001-G

Checksum calculation:
  Input: "PCE" + "SPEC" + "2025" + "0001"
  ASCII sum mod 26 → 'G'
  Expected: G
  Actual:   G
  Result:   ✓ VALID
```

If checksum is wrong:

```
doc_id: PCE-SPEC-2025-0001-X  ✗
# ERROR: INVALID_ID_CHECKSUM
# Expected G, got X
```

### Required Fields for Specs

Specification documents (`doc_type: spec`) must have:
- `version` field
- `owner` field

Missing either will cause a validation error.

## Customization

### Add a New Component

```yaml
COMP:
  type: enum
  values: ["PCE", "KKS", "EDGE", "NEWCOMP"]  # Add new component
  select:
    by_path:
      - pattern: "docs/pce/**"
        value: "PCE"
      - pattern: "docs/kakusill/**"
        value: "KKS"
      - pattern: "docs/edge/**"
        value: "EDGE"
      - pattern: "docs/newcomp/**"     # Add new path
        value: "NEWCOMP"
```

### Add a New Document Type

```yaml
KIND:
  type: enum_from_doc_type
  mapping:
    spec: "SPEC"
    design: "DES"
    memo: "MEMO"
    runbook: "RUN"
    decision: "ADR"
    tutorial: "TUT"  # Add new type
```

## Next Steps

- See [simple](../simple/) for a simpler starting configuration
- See [advanced](../advanced/) for all available features
- Read [User Guide](../../docs/user-guide.md) for complete documentation
