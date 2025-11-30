# Shirushi (標) - Document ID Management System

**Version**: 0.1.0
**Status**: Development

Shirushi is a document ID management and validation system for Git repositories. It ensures consistent, immutable document IDs across Markdown and YAML files, with CI integration to detect ID tampering, duplication, or missing IDs.

## Features

- 🔖 **Consistent ID Format**: Define custom ID formats using flexible dimension-based templates
- ✅ **Validation**: Detect missing, duplicate, or modified document IDs
- 🔍 **CI Integration**: Use as a quality gate in your continuous integration pipeline
- 📊 **Index Management**: Maintain a centralized index of all documents
- 🎯 **Git-Aware**: Compare IDs across Git revisions to prevent unauthorized changes
- 🧩 **Extensible**: Support for multiple dimension types (enum, serial, checksum, etc.)

## Installation

```bash
npm install -g shirushi
# or
pnpm add -g shirushi
# or
yarn global add shirushi
```

## Quick Start

### 1. Create Configuration

Create `.shirushi.yml` in your repository root:

```yaml
# .shirushi.yml

# Files to include
doc_globs:
  - "docs/**/*.md"
  - "docs/**/*.yaml"

# Files to exclude
ignore:
  - "docs/archive/**"
  - "**/*.draft.md"

# ID format template
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"

# Dimension definitions
dimensions:
  COMP:
    type: enum
    values: ["FRONT", "BACK", "GW"]
    select:
      by_path:
        - pattern: "docs/frontend/**"
          value: "FRONT"
        - pattern: "docs/backend/**"
          value: "BACK"
        - pattern: "docs/gateway/**"
          value: "GW"

  KIND:
    type: enum_from_doc_type
    mapping:
      spec: "SPEC"
      design: "DES"
      memo: "MEMO"

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

# Index file location
index_file: "docs/doc_index.yaml"

# Validation rules
forbid_id_change: true
allow_missing_id_in_new_files: false
```

### 2. Add IDs to Documents

**Markdown documents** (with YAML front matter):

```markdown
---
doc_id: FRONT-SPEC-2025-0001-X
title: Boundary Definition
doc_type: spec
status: active
version: "1.0.0"
---

# Boundary Definition

...
```

**YAML documents**:

```yaml
doc_id: BACK-SPEC-2025-0001-Y
title: Backend Service Principles
doc_type: spec
status: draft
version: "0.3.2"

principles:
  - ...
```

### 3. Create Index File

Create `docs/doc_index.yaml`:

```yaml
documents:
  - doc_id: FRONT-SPEC-2025-0001-X
    path: docs/frontend/boundary.md
    title: Boundary Definition
    doc_type: spec
    status: active
    version: "1.0.0"

  - doc_id: BACK-SPEC-2025-0001-Y
    path: docs/backend/principles.yaml
    title: Backend Service Principles
    doc_type: spec
    status: draft
    version: "0.3.2"
```

### 4. Validate

```bash
# Validate all documents
shirushi lint

# Validate with Git comparison (detect ID changes)
shirushi lint --base origin/main

# Scan and output document list
shirushi scan --format table
shirushi scan --format json
```

## CLI Commands

### `shirushi lint`

Validate document IDs and index consistency.

```bash
shirushi lint [options]

Options:
  -b, --base <git-ref>    Compare against a Git revision (e.g., origin/main, HEAD~1)
                          Detects doc_id changes if forbid_id_change is true
  --changed-only          Only validate files that have been modified
                          With --base: files changed between base ref and HEAD
                          Without --base: uncommitted changes (git status)
  -c, --config <path>     Path to .shirushi.yml (default: auto-discover)
  -f, --format <format>   Output format: table, json (default: table)
  -q, --quiet             Quiet mode (only show file paths with errors)
```

**Exit Codes**:
- `0`: Success (no errors)
- `1`: Validation errors found
- `2`: Configuration or runtime error

**Error Codes**:
- `MISSING_ID`: Document missing doc_id field
- `MULTIPLE_IDS_IN_DOCUMENT`: Multiple doc_id fields in one document
- `INVALID_ID_FORMAT`: ID doesn't match expected format
- `INVALID_ID_CHECKSUM`: Checksum validation failed
- `INVALID_ENUM_VALUE`: Enum dimension has invalid value
- `ENUM_SELECTION_MISMATCH`: Path-based enum selection mismatch
- `DOC_ID_CHANGED`: ID changed since base ref (when using --base)
- `DOC_ID_MISMATCH_WITH_INDEX`: Document ID doesn't match index
- `UNINDEXED_DOC_ID`: Document has ID but not in index
- `MISSING_FILE_FOR_INDEX`: Index references non-existent file
- `NOT_A_GIT_REPO`: Current directory is not a Git repository (when using --base or --changed-only)
- `INVALID_GIT_REF`: Specified Git reference does not exist (when using --base)

### `shirushi scan`

Scan and list all documents.

```bash
shirushi scan [options]

Options:
  --format <format>   Output format: table, json, yaml (default: table)
  --config <path>     Path to .shirushi.yml
```

### `shirushi index sync` (Future)

Synchronize index file with documents.

```bash
shirushi index sync [options]

Options:
  --dry-run          Show changes without writing
  --config <path>    Path to .shirushi.yml
```

## CI Integration

### GitHub Actions

```yaml
name: Shirushi DocID Lint

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
          fetch-depth: 0  # Required for --base comparison

      - uses: actions/setup-node@v4
        with:
          node-version: "20"

      - name: Install Shirushi
        run: npm install -g shirushi

      - name: Validate Document IDs
        run: shirushi lint --base origin/${{ github.base_ref }}
```

For faster CI on large repositories, use `--changed-only` to lint only modified files:

```yaml
      - name: Validate Changed Documents
        run: shirushi lint --base origin/${{ github.base_ref }} --changed-only
```

## Dimension Types

Shirushi supports multiple dimension types for flexible ID structures:

### `enum`

Fixed set of allowed values, optionally selected by file path.

```yaml
COMP:
  type: enum
  values: ["FRONT", "BACK", "GW"]
  select:
    by_path:
      - pattern: "docs/frontend/**"
        value: "FRONT"
```

### `enum_from_doc_type`

Values derived from document's `doc_type` metadata field.

```yaml
KIND:
  type: enum_from_doc_type
  mapping:
    spec: "SPEC"
    design: "DES"
    memo: "MEMO"
```

### `year`

Year component, either from document metadata or current date.

```yaml
YEAR4:
  type: year
  digits: 4
  source: "created_at"  # or "now"
  validate:              # Optional
    min: 2000
    max: 2100
```

### `serial`

Sequential number within a defined scope.

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]  # Counter resets per scope
```

### `checksum`

Checksum computed from other dimensions.

```yaml
CHK1:
  type: checksum
  algo: "mod26AZ"  # Currently only mod26AZ supported
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

## Examples

See the `examples/` directory for complete configuration examples:

- [`examples/simple/`](examples/simple/) - Minimal configuration
- [`examples/multi-component/`](examples/multi-component/) - Multi-component project example
- [`examples/getting-started/`](examples/getting-started/) - Beginner tutorial

## Documentation

- [User Guide](docs/user-guide.md) - Detailed usage instructions
- [Developer Guide](docs/developer-guide.md) - Contributing and extending Shirushi
- [Architecture Decision Records](docs/adr/) - Design decisions and rationale
- [API Documentation](docs/api/) - Internal API reference

## Development

```bash
# Clone repository
git clone https://github.com/your-org/shirushi.git
cd shirushi

# Install dependencies
pnpm install

# Run tests
pnpm test

# Run tests with coverage
pnpm test:coverage

# Build
pnpm build

# Run locally
pnpm dev

# Lint
pnpm lint

# Type check
pnpm typecheck
```

## Architecture

Shirushi follows a layered architecture:

```
CLI Layer (Commander.js)
    ↓
Core Logic (Validator, Scanner, Generator)
    ↓
Dimension Handlers (Enum, Year, Serial, Checksum)
    ↓
Parsers (Markdown, YAML, Template)
    ↓
Git Layer (Operations, Diff)
```

See [Architecture Decision Records](docs/adr/) for detailed design decisions.

## Contributing

Contributions are welcome! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

1. Fork the repository
2. Create a feature branch
3. Make your changes with tests
4. Ensure all tests pass and coverage is maintained
5. Submit a pull request

## License

MIT License - see [LICENSE](LICENSE) for details

## Acknowledgments

Shirushi was designed to work alongside document search and reference tools (like KIRI MCP), providing the "ID integrity and index consistency" layer while search tools handle the "discovery and reference" layer.

---

**Shirushi (標)** - Ensuring document identity integrity in your Git repository
