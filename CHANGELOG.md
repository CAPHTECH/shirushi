# Changelog

All notable changes to this project will be documented in this file.

## [0.4.0] - 2025-12-27

### Features
- `shirushi skill` command for AI agent skill distribution
  - Install shirushi skill files for Claude Code, Cursor, Windsurf, Aider, and other agents
  - Support for OpenSkills-compatible directory structure (`.agent/skills/`, `.claude/skills/`)
  - Global installation support (`~/.agent/skills/`, `~/.claude/skills/`)
  - `skill install`, `skill list`, `skill uninstall` subcommands
  - Path traversal protection for security
- `shirushi show <doc_id>` command for document lookup by ID
  - Retrieve document information directly from doc_id
  - Table and JSON output formats
- `shirushi lsp` command for Language Server Protocol integration
  - Jump-to-definition for `@see docid` references in source code
  - Integration with IDE extensions (VS Code, etc.)

## [0.3.0] - 2025-12-21

### Features
- Content integrity validation with SHA-256 hashing
- Checksum suffix for doc_id format (`source_ref_patterns`)
- Enhanced traceability between documents and source references

### CI/CD
- Enforce shirushi lint in dogfood job

## [0.2.0] - 2025-12-18

### Added
- `shirushi assign` command for automatic doc_id generation and embedding
  - Supports all dimension types (enum, enum_from_doc_type, year, serial, checksum)
  - Transaction-based writes with automatic rollback on failure
  - File-based locking to prevent concurrent execution
  - `--dry-run` option for preview without changes
  - `--format json` option for machine-readable output
- New error codes: `ASSIGN_GENERATION_FAILED`, `ASSIGN_WRITE_FAILED`, `ASSIGN_ROLLBACK_FAILED`, `ASSIGN_INDEX_UPDATE_FAILED`, `ASSIGN_VALIDATION_FAILED`, `DIMENSION_HANDLER_CRASH`

### Fixed
- Windows path compatibility for index file entries

## [0.1.0] - 2025-11-30

### Added
- Initial release
- `shirushi lint` command for document validation
- `shirushi scan` command for document listing
- Configuration via `.shirushi.yml`
- Support for Markdown and YAML documents
- Dimension types: enum, enum_from_doc_type, year, serial, checksum
- Index file validation
- Git integration for change detection (`--base`, `--changed-only`)
- Reference integrity checking (`--check-references`)
