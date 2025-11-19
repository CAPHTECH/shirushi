# Shirushi User Guide

This guide will help you get started with Shirushi and use it effectively in your projects.

## Table of Contents

1. [Introduction](#introduction)
2. [Installation](#installation)
3. [Configuration](#configuration)
4. [Document Format](#document-format)
5. [CLI Commands](#cli-commands)
6. [Dimension Types](#dimension-types)
7. [Validation Errors](#validation-errors)
8. [CI Integration](#ci-integration)
9. [Best Practices](#best-practices)
10. [Troubleshooting](#troubleshooting)

---

## Introduction

### What is Shirushi?

Shirushi (標 - "mark" or "sign" in Japanese) is a document ID management system that ensures:

- Every document has a unique, consistent ID
- IDs follow a predefined format
- IDs are not accidentally changed or duplicated
- Your documentation remains well-organized and traceable

### When to Use Shirushi

Use Shirushi when you need to:

- **Track documents across changes**: Know which document is which, even after renaming
- **Reference documents**: Use stable IDs in code comments, issues, or other documents
- **Prevent ID tampering**: Ensure AI/LLM tools or human editors don't accidentally change IDs
- **Enforce standards**: Maintain consistent ID formatting across teams
- **Audit documentation**: Quickly find which documents have changed

---

## Installation

### npm

```bash
npm install -g shirushi
```

### pnpm

```bash
pnpm add -g shirushi
```

### yarn

```bash
yarn global add shirushi
```

### Verify Installation

```bash
shirushi --version
```

---

## Configuration

### Creating `.shirushi.yml`

Create a `.shirushi.yml` file in your repository root:

```yaml
# Files to scan for doc_id
doc_globs:
  - "docs/**/*.md"
  - "docs/**/*.yaml"

# Files to ignore
ignore:
  - "docs/archive/**"
  - "**/*.draft.md"

# Where the index file lives
index_file: "docs/doc_index.yaml"

# ID format template
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"

# Define each dimension
dimensions:
  COMP:
    type: enum
    values: ["PCE", "KKS", "EDGE"]
    select:
      by_path:
        - pattern: "docs/pce/**"
          value: "PCE"
        - pattern: "docs/kakusill/**"
          value: "KKS"

  KIND:
    type: enum_from_doc_type
    mapping:
      spec: "SPEC"
      design: "DES"

  YEAR4:
    type: year
    digits: 4
    source: "created_at"

  SER4:
    type: serial
    digits: 4
    scope: ["COMP", "KIND", "YEAR4"]

  CHK1:
    type: checksum
    algo: "mod26AZ"
    of: ["COMP", "KIND", "YEAR4", "SER4"]

# Validation rules
forbid_id_change: true
allow_missing_id_in_new_files: false
```

### Configuration Fields

| Field | Required | Description |
|-------|----------|-------------|
| `doc_globs` | Yes | Glob patterns for documents to scan |
| `ignore` | No | Patterns to exclude from scanning |
| `index_file` | No | Path to index file (default: `docs/doc_index.yaml`) |
| `id_format` | Yes | Template for document IDs (with `{PLACEHOLDERS}`) |
| `dimensions` | Yes | Definition of each placeholder in `id_format` |
| `forbid_id_change` | No | Prevent ID changes in existing documents (default: `true`) |
| `allow_missing_id_in_new_files` | No | Allow new documents without IDs (default: `false`) |

---

## Document Format

### Markdown Documents

Markdown documents use YAML front matter:

```markdown
---
doc_id: PCE-SPEC-2025-0001-G
title: Boundary Definition
doc_type: spec
status: active
version: "1.0.0"
created_at: "2025-01-15"
owner: "team-pce"
tags:
  - PCE
  - architecture
---

# Boundary Definition

Your content here...
```

**Requirements**:
- Must start with `---`
- Must have `doc_id` field
- Front matter must be valid YAML
- Only one `doc_id` per document

### YAML Documents

YAML documents have `doc_id` at root level:

```yaml
doc_id: KKS-SPEC-2025-0002-F
title: Kakusill Service Principles
doc_type: spec
status: draft
version: "0.3.2"
created_at: "2025-01-16"
owner: "team-kakusill"

principles:
  - principle_1: ...
  - principle_2: ...
```

**Requirements**:
- Must have `doc_id` at root level
- Must be valid YAML
- Only one `doc_id` per document

---

## CLI Commands

### `shirushi lint`

Validate all documents and check index consistency.

```bash
# Basic validation
shirushi lint

# Compare against Git ref (detect ID changes)
shirushi lint --base origin/main
shirushi lint --base HEAD~1

# Only check changed files
shirushi lint --base origin/main --changed-only

# Use specific config file
shirushi lint --config /path/to/.shirushi.yml

# JSON output (for CI)
shirushi lint --format json
```

**Exit Codes**:
- `0`: Success (all documents valid)
- `1`: Validation errors found
- `2`: Configuration or runtime error

### `shirushi scan`

List all documents with their IDs and metadata.

```bash
# Table format (human-readable)
shirushi scan

# JSON format (for tools)
shirushi scan --format json

# YAML format
shirushi scan --format yaml
```

**Output Example** (table format):

```
┌────────────────────────────┬──────────────────────────┬─────────────────────────┬──────────┐
│ doc_id                     │ path                     │ title                   │ status   │
├────────────────────────────┼──────────────────────────┼─────────────────────────┼──────────┤
│ PCE-SPEC-2025-0001-G       │ docs/pce/boundary.md     │ Boundary Definition     │ active   │
│ KKS-SPEC-2025-0002-F       │ docs/kks/principles.yaml │ Service Principles      │ draft    │
└────────────────────────────┴──────────────────────────┴─────────────────────────┴──────────┘
```

---

## Dimension Types

### `enum`

Fixed set of allowed values.

```yaml
COMP:
  type: enum
  values: ["PCE", "KKS", "EDGE"]
```

Optionally, auto-select based on file path:

```yaml
COMP:
  type: enum
  values: ["PCE", "KKS", "EDGE"]
  select:
    by_path:
      - pattern: "docs/pce/**"
        value: "PCE"
      - pattern: "docs/kakusill/**"
        value: "KKS"
      - pattern: "docs/edge/**"
        value: "EDGE"
```

### `enum_from_doc_type`

Derives value from document's `doc_type` field.

```yaml
KIND:
  type: enum_from_doc_type
  mapping:
    spec: "SPEC"        # doc_type: spec → KIND: SPEC
    design: "DES"       # doc_type: design → KIND: DES
    memo: "MEMO"        # doc_type: memo → KIND: MEMO
    runbook: "RUN"
    decision: "ADR"
```

**Requires**: Document must have `doc_type` field.

### `year`

Year component (usually 4 digits).

```yaml
YEAR4:
  type: year
  digits: 4
  source: "created_at"  # Use 'created_at' field from document metadata
```

Or use current year:

```yaml
YEAR2:
  type: year
  digits: 2
  source: "now"  # Use current year when generating ID
```

Optional validation:

```yaml
YEAR4:
  type: year
  digits: 4
  source: "created_at"
  validate:
    min: 2020
    max: 2030
```

### `serial`

Sequential number within a scope.

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]
```

**Example**:
- Scope: `PCE-SPEC-2025`
- Serials: `0001`, `0002`, `0003`, ...

**Note**: Gaps in serial numbers are allowed (e.g., `0001`, `0005`, `0100`).

### `checksum`

Checksum computed from other dimensions.

```yaml
CHK1:
  type: checksum
  algo: "mod26AZ"
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

**Algorithm**: Currently only `mod26AZ` is supported:
- Sums ASCII values of input characters
- Modulo 26
- Maps to A-Z

**Purpose**: Detect accidental ID modifications, not for security.

---

## Validation Errors

### Common Errors

#### `MISSING_ID`

Document doesn't have a `doc_id` field.

**Fix**: Add `doc_id` to your document.

```yaml
doc_id: PCE-SPEC-2025-0001-G  # Add this
title: My Document
```

#### `INVALID_ID_FORMAT`

`doc_id` doesn't match the expected format.

**Example**:
```
Expected: {COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}
Got:      PCE-SPEC-2025-001-G  (wrong serial length)
```

**Fix**: Ensure ID matches format (`0001` not `001`).

#### `INVALID_ID_CHECKSUM`

Checksum doesn't match computed value.

**Example**:
```
Expected checksum: G
Got checksum:      X
```

**Fix**: Recalculate checksum or regenerate ID.

#### `DOC_ID_CHANGED`

ID changed since base Git ref (when using `--base`).

**Example**:
```
File: docs/pce/boundary.md
Old ID: PCE-SPEC-2025-0001-G
New ID: PCE-SPEC-2025-0002-H
```

**Fix**: This is usually intentional. If not, revert the change.

#### `DOC_ID_MISMATCH_WITH_INDEX`

Document ID doesn't match index.

**Example**:
```
Document: PCE-SPEC-2025-0001-G
Index:    PCE-SPEC-2025-0999-X
```

**Fix**: Run `shirushi index sync` (v0.2) to update index.

#### `UNINDEXED_DOC_ID`

Document has ID but isn't in index.

**Fix**: Run `shirushi index sync` to add it.

---

## CI Integration

### GitHub Actions

```yaml
name: Shirushi Lint

on:
  pull_request:
    paths:
      - "docs/**"
      - ".shirushi.yml"

jobs:
  docid-lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0  # Required for --base

      - uses: actions/setup-node@v4
        with:
          node-version: "20"

      - name: Install Shirushi
        run: npm install -g shirushi

      - name: Validate Document IDs
        run: shirushi lint --base origin/${{ github.base_ref }}
```

### GitLab CI

```yaml
docid-lint:
  stage: test
  image: node:20
  script:
    - npm install -g shirushi
    - shirushi lint --base origin/main
  only:
    changes:
      - docs/**
      - .shirushi.yml
```

### Pre-commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Run Shirushi lint on staged files
shirushi lint --changed-only

if [ $? -ne 0 ]; then
  echo "Shirushi validation failed. Aborting commit."
  exit 1
fi
```

---

## Best Practices

### 1. Use Descriptive Dimension Names

**Good**:
```yaml
id_format: "{COMPONENT}-{DOCTYPE}-{YEAR}-{SERIAL}-{CHECK}"
```

**Bad**:
```yaml
id_format: "{A}-{B}-{C}-{D}-{E}"
```

### 2. Keep IDs Short but Readable

**Good**: `PCE-SPEC-2025-0001-G` (23 characters)
**Too Long**: `PRODUCTCATALOGENGINE-SPECIFICATION-2025-0001-G` (49 characters)

### 3. Use Path-Based Enum Selection

Instead of manual assignment:

```yaml
COMP:
  type: enum
  values: ["PCE", "KKS"]
  select:
    by_path:
      - pattern: "docs/pce/**"
        value: "PCE"
```

This auto-validates that documents are in the right directory.

### 4. Document Your ID Format

Add comments to `.shirushi.yml`:

```yaml
# ID Format: COMP-KIND-YEAR-SERIAL-CHECKSUM
# Example: PCE-SPEC-2025-0001-G
#
# COMP: Component (PCE, KKS, EDGE)
# KIND: Document type (SPEC, DES, MEMO)
# YEAR: Year created (4 digits)
# SERIAL: Sequential number within scope (4 digits)
# CHECKSUM: mod26AZ checksum (1 letter A-Z)
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"
```

### 5. Run Validation in CI

Always run `shirushi lint` in your CI pipeline to catch issues early.

### 6. Commit Index with Documents

When adding/modifying documents, always commit both:

```bash
git add docs/new-document.md docs/doc_index.yaml
git commit -m "Add new document"
```

### 7. Use `--base` in Pull Requests

Detect ID changes in PRs:

```bash
shirushi lint --base origin/main
```

---

## Troubleshooting

### "Cannot find .shirushi.yml"

**Problem**: Shirushi can't find your configuration file.

**Solutions**:
1. Ensure `.shirushi.yml` is in your repository root
2. Or use `--config` flag: `shirushi lint --config path/to/.shirushi.yml`
3. Check file name (not `.shirushi.yaml` or `shirushi.yml`)

### "Invalid YAML in .shirushi.yml"

**Problem**: Configuration file has syntax errors.

**Solutions**:
1. Validate YAML online: https://www.yamllint.com/
2. Check indentation (use spaces, not tabs)
3. Ensure strings with special characters are quoted

### "Dimension referenced in id_format not defined"

**Problem**: Your `id_format` uses a placeholder not in `dimensions`.

**Example**:
```yaml
id_format: "{COMP}-{UNKNOWN}-{YEAR}"
# But no UNKNOWN in dimensions
```

**Solution**: Add the missing dimension or fix the format.

### "Checksum always fails"

**Problem**: You're manually creating IDs with wrong checksums.

**Solutions**:
1. Use a checksum calculator (future: `shirushi generate-checksum`)
2. Temporarily remove checksum dimension while creating IDs manually
3. Wait for v0.2 `shirushi assign` command

### Index Always Out of Sync

**Problem**: Index file doesn't match documents.

**Solution**: Wait for v0.2 `shirushi index sync` command, or manually update index.

---

## Next Steps

- Read [Developer Guide](developer-guide.md) to extend Shirushi
- Check [Examples](../examples/) for real-world configurations
- Review [Architecture Decision Records](adr/) to understand design choices

---

For more help, see:
- [GitHub Issues](https://github.com/your-org/shirushi/issues)
- [Discussions](https://github.com/your-org/shirushi/discussions)
