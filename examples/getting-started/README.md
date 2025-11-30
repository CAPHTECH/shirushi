# Getting Started Example

A minimal Shirushi configuration to help you understand the basics.

## Quick Start

```bash
# Navigate to this directory
cd examples/getting-started

# Validate all documents
npx shirushi lint

# List all documents
npx shirushi scan
```

## Project Structure

```
getting-started/
├── .shirushi.yml          # Configuration file
├── README.md              # This file
└── docs/
    ├── doc_index.yaml     # Document index
    ├── welcome.md         # First document (DOC-2025-0001)
    └── second-doc.md      # Second document (DOC-2025-0002)
```

## ID Format

This example uses a simple 3-part ID format:

```
{KIND}-{YEAR4}-{SER4}
```

Example: `DOC-2025-0001`

| Part | Description | Example |
|------|-------------|---------|
| KIND | Document type | DOC |
| YEAR4 | 4-digit year | 2025 |
| SER4 | Serial number (4 digits) | 0001 |

## Try These Commands

### Validate Documents

```bash
npx shirushi lint
```

Expected output:
```
Validated 2 documents
✓ All documents are valid
```

### List Documents

```bash
npx shirushi scan
```

Expected output:
```
DOC-2025-0001  docs/welcome.md      Welcome to Shirushi
DOC-2025-0002  docs/second-doc.md   Second Document Example
```

## Next Steps

1. **Add a new document**: Create a new `.md` file in `docs/` with a unique `doc_id`
2. **Update the index**: Add the new document to `docs/doc_index.yaml`
3. **Validate**: Run `shirushi lint` to ensure everything is correct
4. **Explore advanced features**: See `examples/multi-component/` for a more complex setup

## Configuration Explained

```yaml
# .shirushi.yml

doc_globs:
  - "docs/**/*.md"    # Find all .md files in docs/

id_format: "{KIND}-{YEAR4}-{SER4}"  # ID template

dimensions:
  KIND:
    type: enum
    values: ["DOC"]   # Only one type: DOC

  YEAR4:
    type: year
    digits: 4
    source: now       # Use current year

  SER4:
    type: serial
    digits: 4
    scope: ["KIND", "YEAR4"]  # Reset each year
```

## Common Issues

### "MISSING_ID" Error

The document doesn't have a `doc_id` in its front matter.

**Fix**: Add a valid `doc_id` to the YAML front matter:

```yaml
---
doc_id: DOC-2025-0003
title: Your Document Title
---
```

### "MALFORMED_ID" Error

The `doc_id` doesn't match the expected format.

**Fix**: Ensure the ID follows `DOC-YYYY-NNNN` format.

### "DOC_ID_MISMATCH_WITH_INDEX" Error

The document's `doc_id` doesn't match what's in `doc_index.yaml`.

**Fix**: Update `doc_index.yaml` to match the document's `doc_id`.
