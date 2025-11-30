# Multi-Component Configuration Example

This example demonstrates a multi-component project setup with path-based component selection and checksum validation.

## Project Structure

This example simulates a project with three components:

- **FRONT** (Frontend) - `docs/frontend/`
- **BACK** (Backend) - `docs/backend/`
- **GW** (Gateway) - `docs/gateway/`

## ID Format

```
{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}
```

**Example IDs**:
- `FRONT-SPEC-2025-0001-X` - Frontend specification #1 from 2025
- `BACK-SPEC-2025-0001-Y` - Backend specification #1 from 2025
- `GW-ADR-2025-0001-Z` - Gateway ADR #1 from 2025

## Dimensions

### COMP (enum with path selection)

Component identifier automatically determined by file path.

**Values**:
- `FRONT` - Files in `docs/frontend/**`
- `BACK` - Files in `docs/backend/**`
- `GW` - Files in `docs/gateway/**`

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
- `FRONT-SPEC-2025`: 0001, 0002, 0003, ...
- `FRONT-DES-2025`: 0001, 0002, 0003, ... (separate counter)
- `BACK-SPEC-2025`: 0001, 0002, 0003, ... (separate counter)

### CHK1 (checksum)

Single character (A-Z) checksum using mod26AZ algorithm.

**Purpose**: Detect accidental ID modifications.

## Usage

### Validate Documents

```bash
shirushi lint --config examples/multi-component/.shirushi.yml
```

### Scan Documents

```bash
shirushi scan --config examples/multi-component/.shirushi.yml --format table
```

### Compare with Git Base

```bash
shirushi lint --config examples/multi-component/.shirushi.yml --base origin/main
```

## File Organization

```
docs/
├── frontend/               # Frontend component documents
│   └── boundary.md         # doc_id: FRONT-SPEC-2025-0001-X
│
├── backend/                # Backend component documents
│   └── principles.yaml     # doc_id: BACK-SPEC-2025-0001-Y
│
├── gateway/                # Gateway component documents
│   └── adr/
│       └── 0001-graphql.md # doc_id: GW-ADR-2025-0001-Z
│
└── doc_index.yaml          # Central index
```

## Validation Features

### Path-Based Component Validation

Documents in `docs/frontend/` **must** have `COMP = FRONT` in their doc_id.

**Valid**:
```
# File: docs/frontend/boundary.md
doc_id: FRONT-SPEC-2025-0001-X  ✓
```

**Invalid**:
```
# File: docs/frontend/boundary.md
doc_id: BACK-SPEC-2025-0001-X  ✗
# ERROR: ENUM_SELECTION_MISMATCH
# Expected COMP=FRONT for path docs/frontend/**, got BACK
```

### Checksum Validation

Checksums are automatically validated.

If checksum is wrong:
```
doc_id: FRONT-SPEC-2025-0001-Z  ✗
# ERROR: INVALID_ID_CHECKSUM
# Expected X, got Z
```

## Customization

### Add a New Component

```yaml
COMP:
  type: enum
  values: ["FRONT", "BACK", "GW", "MOBILE"]  # Add new component
  select:
    by_path:
      - pattern: "docs/frontend/**"
        value: "FRONT"
      - pattern: "docs/backend/**"
        value: "BACK"
      - pattern: "docs/gateway/**"
        value: "GW"
      - pattern: "docs/mobile/**"       # Add new path
        value: "MOBILE"
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
- See [getting-started](../getting-started/) for a beginner tutorial
- Read [User Guide](../../docs/user-guide.md) for complete documentation
