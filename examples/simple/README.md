# Simple Configuration Example

This is a minimal Shirushi configuration suitable for small projects with basic ID requirements.

## ID Format

```
{TYPE}-{YEAR}-{NUM}
```

**Example IDs**:
- `SPEC-2025-0001` - First specification in 2025
- `DOC-2025-0001` - First general document in 2025
- `MEMO-2025-0001` - First memo in 2025
- `SPEC-2025-0002` - Second specification in 2025

## Dimensions

### TYPE (enum)

Document type code.

**Values**:
- `SPEC` - Specifications
- `DOC` - General documentation
- `MEMO` - Memos/notes
- `GUIDE` - User guides

### YEAR (year)

4-digit year from document's `created_at` field.

### NUM (serial)

4-digit sequential number, scoped by `TYPE` and `YEAR`.

**Example**: `SPEC-2025` counter: 0001, 0002, 0003, ...

## Usage

### Create a Document

```markdown
---
doc_id: SPEC-2025-0001
title: System Architecture
created_at: "2025-01-15"
---

# System Architecture

Your content here...
```

### Validate

```bash
shirushi lint --config examples/simple/.shirushi.yml
```

### Scan

```bash
shirushi scan --config examples/simple/.shirushi.yml
```

## Index File

The `docs/doc_index.yaml` tracks all documents:

```yaml
documents:
  - doc_id: SPEC-2025-0001
    path: docs/architecture.md
    title: System Architecture
    created_at: "2025-01-15"

  - doc_id: DOC-2025-0001
    path: docs/user-guide.md
    title: User Guide
    created_at: "2025-01-20"
```

## Customization

### Add More Document Types

```yaml
TYPE:
  type: enum
  values:
    - "SPEC"
    - "DOC"
    - "MEMO"
    - "GUIDE"
    - "RFC"     # Add Request for Comments
    - "ADR"     # Add Architecture Decision Records
```

### Change Serial Scope

To have a global counter (not reset per type):

```yaml
NUM:
  type: serial
  digits: 4
  scope: ["YEAR"]  # Only scoped by year
```

This would give you:
- `SPEC-2025-0001`
- `DOC-2025-0002` (continues from 0001)
- `MEMO-2025-0003` (continues from 0002)

### Add Checksum

For additional validation:

```yaml
id_format: "{TYPE}-{YEAR}-{NUM}-{CHK}"

dimensions:
  TYPE:
    # ... (same as before)

  YEAR:
    # ... (same as before)

  NUM:
    # ... (same as before)

  CHK:
    type: checksum
    algo: "mod26AZ"
    of: ["TYPE", "YEAR", "NUM"]
```

This adds a checksum character (A-Z) to detect ID modifications.

## Next Steps

- Read [User Guide](../../docs/user-guide.md) for detailed documentation
- Try [pce-kakusill-edge](../pce-kakusill-edge/) for a more complex example
- See [advanced](../advanced/) for all features
