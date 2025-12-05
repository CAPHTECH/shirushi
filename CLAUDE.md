# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Shirushi (標 - "mark" in Japanese) is a document ID management and validation system for Git repositories. It ensures consistent, immutable document IDs across Markdown and YAML files, with CI integration to detect ID tampering, duplication, or missing IDs.

**Current Status**: v0.1.0 - Documentation phase complete, implementation not yet started.

GitHub: CAPHTECH/shirushi

## Development Commands

### Build & Development
```bash
pnpm dev              # Watch mode (auto-rebuild)
pnpm build            # Build CLI tool with tsup
pnpm clean            # Clean dist directory
```

### Testing
```bash
pnpm test             # Run all tests with vitest
pnpm test:ui          # Run tests with UI
pnpm test:coverage    # Run tests with coverage (80% minimum)
pnpm test:mutation    # Run mutation tests with Stryker

# Run specific test file
pnpm test -- dimension.test.ts

# Watch mode for testing
pnpm test --watch
```

### Code Quality
```bash
pnpm lint             # Lint TypeScript files
pnpm lint:fix         # Auto-fix linting issues
pnpm typecheck        # Type check without emitting
pnpm format           # Format code with Prettier
pnpm format:check     # Check formatting
```

### Dogfooding
```bash
pnpm shirushi:lint    # Run Shirushi on itself
pnpm shirushi:scan    # Scan Shirushi's own docs
```

## Architecture

### Layered Architecture

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

### Key Architectural Decisions (ADRs)

Critical decisions documented in `docs/adr/`:

1. **ADR-0001**: Use discriminated unions for dimension types (type safety)
2. **ADR-0002**: Use Zod for configuration validation (runtime validation + type inference)
3. **ADR-0003**: Document is source of truth for doc_id (index is derived)
4. **ADR-0004**: Use simple mod26AZ checksum (not cryptographic)
5. **ADR-0005**: Defer `assign` command to v0.2 (validation first)
6. **ADR-0006**: No gap validation for serial numbers (operational flexibility)
7. **ADR-0007**: Manual index synchronization only (`lint` is read-only)

### Planned Directory Structure

```
src/
├── cli/              # CLI commands (lint, scan)
├── core/             # Validation, scanning, ID generation
├── dimensions/       # Dimension type handlers
│   └── handlers/     # enum, year, serial, checksum
├── parsers/          # Markdown, YAML, template parsers
├── config/           # Configuration loading & validation
├── git/              # Git operations and diff detection
├── errors/           # Error classes and codes
├── types/            # TypeScript type definitions
└── utils/            # Logging, glob, regex utilities
```

## Core Concepts

### Dimension System

Shirushi uses a **dimension-based ID format**. Each dimension is a component of the doc_id:

```yaml
id_format: "{COMP}-{KIND}-{YEAR4}-{SER4}-{CHK1}"
# Example: PCE-SPEC-2025-0001-G
```

**Dimension Types** (each has a dedicated handler):
- `enum`: Fixed set of values (e.g., component names)
- `enum_from_doc_type`: Derived from document's `doc_type` field
- `year`: Year component (from metadata or current)
- `serial`: Sequential number within scope
- `checksum`: Computed checksum (mod26AZ algorithm)

### Handler Interface

Each dimension type implements:
```typescript
interface DimensionHandler<T extends Dimension> {
  validate(value: string, dimension: T, context: ValidationContext): ValidationResult;
  generate(dimension: T, context: GenerationContext): string;
  toPattern(dimension: T): string; // For regex generation
}
```

### Configuration Validation

Configuration (`.shirushi.yml`) is validated using **Zod schemas** which provide:
- Runtime validation
- TypeScript type inference
- Clear error messages

The config schema uses discriminated unions matching the dimension types.

### Configurable ID Field Name

The field name for document IDs is configurable via `id_field` (default: `"doc_id"`):

```yaml
id_field: "document_id"  # Use "document_id" instead of "doc_id"
```

Both documents and index file use the same configured field name.

### ID Validation Flow

1. Parse `id_format` template to extract placeholders
2. Generate regex pattern from dimension definitions
3. Parse doc_id using generated regex
4. Validate each dimension using its handler
5. Validate checksum (if present)
6. Validate against index file
7. If `--base` flag: compare with Git ref to detect changes

### Document vs Index

**Critical principle**: Document is source of truth (ADR-0003)
- Documents contain the authoritative `doc_id`
- Index file (`docs/doc_index.yaml`) is a derived artifact
- Mismatches are reported as `DOC_ID_MISMATCH_WITH_INDEX`
- Index sync is manual (ADR-0007), not automatic

## v0.1 Scope

**Implemented**:
- `shirushi lint` - Validation command (read-only)
- `shirushi scan` - Document listing
- Core ID generation logic (internal, not CLI-exposed)

**Deferred to v0.2** (ADR-0005):
- `shirushi assign` - Automatic ID assignment
- `shirushi index sync` - Index synchronization

## TypeScript Patterns

### Discriminated Unions

Used extensively for type-safe dimension handling:
```typescript
type Dimension =
  | { type: 'enum'; values: string[]; ... }
  | { type: 'year'; digits: number; ... }
  | { type: 'serial'; digits: number; scope: string[]; ... }
  // Exhaustively checked in switch statements
```

### Zod Type Inference

Config types are inferred from Zod schemas:
```typescript
const ConfigSchema = z.object({
  id_format: z.string(),
  dimensions: z.record(DimensionSchema),
  // ...
});

type ShirushiConfig = z.infer<typeof ConfigSchema>;
```

## Testing Strategy

### Test Pyramid
- **80% Unit tests**: Individual modules (parsers, validators, handlers)
- **15% Integration tests**: Multiple modules together
- **5% E2E tests**: Full CLI commands

### Property-Based Testing

Use `fast-check` for dimension validation:
```typescript
// Example: All generated IDs must validate
fc.assert(
  fc.property(validConfigArbitrary, (config) => {
    const id = generateId(config, metadata);
    const result = validateId(id, config);
    expect(result.valid).toBe(true);
  })
);
```

### Coverage Requirements

- Minimum: 80% coverage (enforced in CI)
- Mutation testing with Stryker for critical modules

## Path Aliases

Configured in `tsconfig.json`:
```typescript
import { loadConfig } from '@/config/loader';
import type { Document } from '@/types/document';
```

## Error Handling

Use structured error codes:
```typescript
// Error codes defined in src/errors/codes.ts
'MISSING_ID'
'INVALID_ID_FORMAT'
'INVALID_ID_CHECKSUM'
'DOC_ID_CHANGED'
'DOC_ID_MISMATCH_WITH_INDEX'
// ... etc
```

## Implementation Phases

**Phase 1** (Current): Foundation
- Project setup, config schema, template parser, dimension types (structure only)

**Phase 2**: Parsers
- Markdown/YAML parsers, document scanner

**Phase 3**: Validation
- Dimension handlers, regex generator, ID validator, index validator

**Phase 4**: Git Integration
- Git operations, diff detection

**Phase 5**: CLI
- Commander.js setup, lint/scan commands, formatters

**Phase 6**: Testing & Polish
- Full test suite, documentation

## Key Files

- `specifications.md`: Original Japanese specification (source of truth)
- `docs/adr/`: All architectural decisions
- `docs/user-guide.md`: End-user documentation
- `docs/developer-guide.md`: Extension guide
- `examples/`: Working configuration examples

## Checksum Algorithm

The `mod26AZ` checksum (ADR-0004) is intentionally simple:
```typescript
// Sum ASCII values, mod 26, map to A-Z
function mod26AZ(input: string): string {
  const sum = input.split('').reduce((acc, char) =>
    acc + char.charCodeAt(0), 0);
  return String.fromCharCode(65 + (sum % 26));
}
```

**Purpose**: Detect accidental modifications, NOT cryptographic security.

## References

- Specification: `docs/specifications.md` (Japanese)
- User Guide: `docs/user-guide.md`
- Developer Guide: `docs/developer-guide.md`
- ADRs: `docs/adr/`
- Examples: `examples/simple/`, `examples/multi-component/`
