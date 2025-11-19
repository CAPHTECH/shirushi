# Shirushi Developer Guide

This guide explains how to contribute to Shirushi, extend its functionality, and understand its internal architecture.

## Table of Contents

1. [Getting Started](#getting-started)
2. [Project Structure](#project-structure)
3. [Architecture Overview](#architecture-overview)
4. [Core Concepts](#core-concepts)
5. [Adding a New Dimension Type](#adding-a-new-dimension-type)
6. [Testing Strategy](#testing-strategy)
7. [Code Style](#code-style)
8. [Contributing](#contributing)
9. [Interface Design](#interface-design)

---

## Getting Started

### Prerequisites

- Node.js 18 or higher
- pnpm (recommended) or npm
- Git

### Setup Development Environment

```bash
# Clone repository
git clone https://github.com/your-org/shirushi.git
cd shirushi

# Install dependencies
pnpm install

# Build project
pnpm build

# Run tests
pnpm test

# Run tests with coverage
pnpm test:coverage

# Run linter
pnpm lint

# Type check
pnpm typecheck
```

### Development Workflow

```bash
# Watch mode (auto-rebuild on changes)
pnpm dev

# Run locally
node dist/cli/index.js lint --config ./test-fixtures/basic/.shirushi.yml

# Or use npm link to test globally
npm link
shirushi lint
```

---

## Project Structure

```
shirushi/
├── src/
│   ├── cli/                    # CLI commands and entry point
│   │   ├── index.ts            # CLI entry point
│   │   ├── commands/           # Command implementations
│   │   │   ├── lint.ts
│   │   │   ├── scan.ts
│   │   │   └── index/          # Index-related commands (future)
│   │   └── output/             # Output formatters
│   │       ├── formatters.ts   # JSON, YAML, table formatters
│   │       └── reporters.ts    # Error reporting
│   │
│   ├── core/                   # Core business logic
│   │   ├── validator.ts        # Main validation orchestrator
│   │   ├── scanner.ts          # Document scanning
│   │   ├── generator.ts        # ID generation (internal, v0.1)
│   │   └── index-manager.ts    # Index file operations
│   │
│   ├── dimensions/             # Dimension type handlers
│   │   ├── index.ts            # Dimension registry
│   │   ├── types.ts            # Dimension type definitions
│   │   └── handlers/           # Individual dimension handlers
│   │       ├── base.ts         # Base handler interface
│   │       ├── enum.ts
│   │       ├── enum-from-doc-type.ts
│   │       ├── year.ts
│   │       ├── serial.ts
│   │       └── checksum.ts
│   │
│   ├── parsers/                # Document and format parsers
│   │   ├── markdown.ts         # Markdown front matter parser
│   │   ├── yaml.ts             # YAML parser
│   │   └── template.ts         # id_format template parser
│   │
│   ├── config/                 # Configuration handling
│   │   ├── loader.ts           # Config file loading
│   │   ├── schema.ts           # Zod schemas
│   │   └── validator.ts        # Config validation
│   │
│   ├── git/                    # Git operations
│   │   ├── operations.ts       # Git commands wrapper
│   │   └── diff.ts             # Diff detection for --base
│   │
│   ├── errors/                 # Error handling
│   │   ├── types.ts            # Error class hierarchy
│   │   └── codes.ts            # Error code constants
│   │
│   ├── types/                  # TypeScript type definitions
│   │   ├── config.ts           # Configuration types
│   │   ├── document.ts         # Document types
│   │   ├── index.ts            # Index file types
│   │   ├── validation.ts       # Validation result types
│   │   └── dimension.ts        # Dimension types
│   │
│   └── utils/                  # Utility functions
│       ├── logger.ts           # Structured logging
│       ├── glob.ts             # Glob utilities
│       └── regex.ts            # Regex utilities
│
├── tests/                      # Test files
│   ├── unit/                   # Unit tests (per module)
│   ├── integration/            # Integration tests
│   ├── fixtures/               # Test fixtures
│   └── setup.ts                # Test setup
│
├── docs/                       # Documentation
│   ├── adr/                    # Architecture Decision Records
│   ├── user-guide.md
│   ├── developer-guide.md      # This file
│   └── api/                    # API documentation
│
├── examples/                   # Example configurations
│   ├── simple/
│   ├── pce-kakusill-edge/
│   └── advanced/
│
├── .shirushi.yml               # Self-hosting config
├── package.json
├── tsconfig.json
├── vitest.config.ts
└── README.md
```

---

## Architecture Overview

Shirushi follows a **layered architecture**:

```
┌─────────────────────────────────────┐
│         CLI Layer                   │
│  (Commander.js, output formatters)  │
└─────────────────────────────────────┘
                 ↓
┌─────────────────────────────────────┐
│         Core Logic Layer            │
│ (Validator, Scanner, Generator)     │
└─────────────────────────────────────┘
                 ↓
┌─────────────────────────────────────┐
│      Dimension Handlers Layer       │
│  (Enum, Year, Serial, Checksum)     │
└─────────────────────────────────────┘
                 ↓
┌─────────────────────────────────────┐
│         Parsers Layer               │
│  (Markdown, YAML, Template)         │
└─────────────────────────────────────┘
                 ↓
┌─────────────────────────────────────┐
│          Git Layer                  │
│  (Operations, Diff detection)       │
└─────────────────────────────────────┘
```

### Key Principles

1. **Separation of Concerns**: Each layer has a clear responsibility
2. **Dependency Inversion**: Upper layers depend on abstractions, not concrete implementations
3. **Type Safety**: Extensive use of TypeScript for compile-time guarantees
4. **Testability**: Each module is independently testable

---

## Core Concepts

### Dimension Handlers

Each dimension type has a handler implementing this interface:

```typescript
// src/dimensions/handlers/base.ts
export interface DimensionHandler<T extends Dimension> {
  /**
   * Validate a dimension value
   */
  validate(
    value: string,
    dimension: T,
    context: ValidationContext
  ): Promise<ValidationResult>;

  /**
   * Generate a dimension value (for ID generation)
   */
  generate(
    dimension: T,
    context: GenerationContext
  ): Promise<string>;

  /**
   * Convert dimension to regex pattern (for ID parsing)
   */
  toPattern(dimension: T): string;
}
```

### Configuration Schema

Configuration is validated using Zod schemas:

```typescript
// src/config/schema.ts
import { z } from 'zod';

export const EnumDimensionSchema = z.object({
  type: z.literal('enum'),
  values: z.array(z.string()).min(1),
  select: z.object({
    by_path: z.array(
      z.object({
        pattern: z.string(),
        value: z.string(),
      })
    ),
  }).optional(),
});

export const DimensionSchema = z.discriminatedUnion('type', [
  EnumDimensionSchema,
  EnumFromDocTypeDimensionSchema,
  YearDimensionSchema,
  SerialDimensionSchema,
  ChecksumDimensionSchema,
]);

export const ConfigSchema = z.object({
  doc_globs: z.array(z.string()).min(1),
  id_format: z.string(),
  dimensions: z.record(z.string(), DimensionSchema),
  index_file: z.string().default('docs/doc_index.yaml'),
  forbid_id_change: z.boolean().default(true),
  allow_missing_id_in_new_files: z.boolean().default(false),
});

// Type inference from schema
export type ShirushiConfig = z.infer<typeof ConfigSchema>;
export type Dimension = z.infer<typeof DimensionSchema>;
```

### Validation Flow

```typescript
// Simplified validation flow
async function validateDocument(
  doc: Document,
  config: ShirushiConfig,
  index: DocumentIndex
): Promise<ValidationResult[]> {
  const errors: ValidationResult[] = [];

  // 1. Parse doc_id using generated regex
  const parts = parseDocId(doc.doc_id, config);

  // 2. Validate each dimension
  for (const [name, dimension] of Object.entries(config.dimensions)) {
    const value = parts[name];
    const handler = getDimensionHandler(dimension.type);

    const result = await handler.validate(value, dimension, {
      documentPath: doc.path,
      documentMeta: doc.metadata,
      index,
      config,
    });

    if (!result.valid) {
      errors.push(result);
    }
  }

  // 3. Validate against index
  const indexResult = validateAgainstIndex(doc, index);
  if (!indexResult.valid) {
    errors.push(indexResult);
  }

  return errors;
}
```

---

## Adding a New Dimension Type

Let's add a new dimension type: `region` (for geographic regions).

### Step 1: Define the Type

```typescript
// src/types/dimension.ts
export interface RegionDimension extends BaseDimension {
  type: 'region';
  values: string[]; // e.g., ["US", "EU", "APAC"]
  default?: string; // Default region if not specified
}

// Update Dimension union type
export type Dimension =
  | EnumDimension
  | EnumFromDocTypeDimension
  | YearDimension
  | SerialDimension
  | ChecksumDimension
  | RegionDimension; // Add this
```

### Step 2: Create Zod Schema

```typescript
// src/config/schema.ts
export const RegionDimensionSchema = z.object({
  type: z.literal('region'),
  values: z.array(z.string()).min(1),
  default: z.string().optional(),
});

// Update DimensionSchema
export const DimensionSchema = z.discriminatedUnion('type', [
  EnumDimensionSchema,
  EnumFromDocTypeDimensionSchema,
  YearDimensionSchema,
  SerialDimensionSchema,
  ChecksumDimensionSchema,
  RegionDimensionSchema, // Add this
]);
```

### Step 3: Implement Handler

```typescript
// src/dimensions/handlers/region.ts
import type { DimensionHandler } from './base';
import type { RegionDimension } from '@/types/dimension';
import type { ValidationContext, GenerationContext } from '@/types/validation';

export class RegionHandler implements DimensionHandler<RegionDimension> {
  async validate(
    value: string,
    dimension: RegionDimension,
    context: ValidationContext
  ): Promise<ValidationResult> {
    // Check if value is in allowed values
    if (!dimension.values.includes(value)) {
      return {
        valid: false,
        error: 'INVALID_REGION_VALUE',
        message: `Region "${value}" not in allowed values: ${dimension.values.join(', ')}`,
      };
    }

    return { valid: true };
  }

  async generate(
    dimension: RegionDimension,
    context: GenerationContext
  ): Promise<string> {
    // Check if document metadata has 'region' field
    if (context.documentMeta.region) {
      const region = String(context.documentMeta.region).toUpperCase();

      if (dimension.values.includes(region)) {
        return region;
      }
    }

    // Fall back to default
    if (dimension.default) {
      return dimension.default;
    }

    // No default, use first value
    return dimension.values[0];
  }

  toPattern(dimension: RegionDimension): string {
    // Generate regex pattern: (US|EU|APAC)
    const alternatives = dimension.values.join('|');
    return `(${alternatives})`;
  }
}
```

### Step 4: Register Handler

```typescript
// src/dimensions/index.ts
import { RegionHandler } from './handlers/region';

export class DimensionRegistry {
  private handlers = new Map<string, DimensionHandler<any>>();

  constructor() {
    this.registerDefaultHandlers();
  }

  private registerDefaultHandlers() {
    this.register('enum', new EnumHandler());
    this.register('enum_from_doc_type', new EnumFromDocTypeHandler());
    this.register('year', new YearHandler());
    this.register('serial', new SerialHandler());
    this.register('checksum', new ChecksumHandler());
    this.register('region', new RegionHandler()); // Add this
  }

  register(type: string, handler: DimensionHandler<any>): void {
    this.handlers.set(type, handler);
  }

  get(type: string): DimensionHandler<any> {
    const handler = this.handlers.get(type);
    if (!handler) {
      throw new Error(`No handler registered for dimension type: ${type}`);
    }
    return handler;
  }
}
```

### Step 5: Write Tests

```typescript
// tests/unit/dimensions/region.test.ts
import { describe, it, expect } from 'vitest';
import { RegionHandler } from '@/dimensions/handlers/region';

describe('RegionHandler', () => {
  const handler = new RegionHandler();

  describe('validate', () => {
    it('should accept valid region value', async () => {
      const dimension = {
        type: 'region' as const,
        values: ['US', 'EU', 'APAC'],
      };

      const result = await handler.validate('US', dimension, {} as any);

      expect(result.valid).toBe(true);
    });

    it('should reject invalid region value', async () => {
      const dimension = {
        type: 'region' as const,
        values: ['US', 'EU', 'APAC'],
      };

      const result = await handler.validate('INVALID', dimension, {} as any);

      expect(result.valid).toBe(false);
      expect(result.error).toBe('INVALID_REGION_VALUE');
    });
  });

  describe('generate', () => {
    it('should use region from document metadata', async () => {
      const dimension = {
        type: 'region' as const,
        values: ['US', 'EU', 'APAC'],
      };

      const context = {
        documentMeta: { region: 'eu' }, // lowercase
      } as any;

      const result = await handler.generate(dimension, context);

      expect(result).toBe('EU'); // Uppercased
    });

    it('should use default when metadata missing', async () => {
      const dimension = {
        type: 'region' as const,
        values: ['US', 'EU', 'APAC'],
        default: 'US',
      };

      const context = {
        documentMeta: {},
      } as any;

      const result = await handler.generate(dimension, context);

      expect(result).toBe('US');
    });
  });

  describe('toPattern', () => {
    it('should generate correct regex pattern', () => {
      const dimension = {
        type: 'region' as const,
        values: ['US', 'EU', 'APAC'],
      };

      const pattern = handler.toPattern(dimension);

      expect(pattern).toBe('(US|EU|APAC)');
    });
  });
});
```

### Step 6: Document Usage

```yaml
# Example configuration using region dimension
id_format: "{REGION}-{COMP}-{YEAR}-{SER}-{CHK}"

dimensions:
  REGION:
    type: region
    values: ["US", "EU", "APAC"]
    default: "US"

  # ... other dimensions
```

---

## Testing Strategy

### Test Pyramid

```
         /\
        /  \  E2E Tests (5%)
       /----\
      /      \  Integration Tests (15%)
     /--------\
    /          \  Unit Tests (80%)
   /-----------\
```

### Unit Tests

Test individual modules in isolation:

```typescript
// tests/unit/parsers/template.test.ts
import { describe, it, expect } from 'vitest';
import { parseTemplate } from '@/parsers/template';

describe('parseTemplate', () => {
  it('should extract placeholders from template', () => {
    const template = '{COMP}-{KIND}-{YEAR}';
    const placeholders = parseTemplate(template);

    expect(placeholders).toEqual(['COMP', 'KIND', 'YEAR']);
  });

  it('should handle templates with no placeholders', () => {
    const template = 'STATIC-ID';
    const placeholders = parseTemplate(template);

    expect(placeholders).toEqual([]);
  });
});
```

### Integration Tests

Test multiple modules working together:

```typescript
// tests/integration/validation.test.ts
import { describe, it, expect } from 'vitest';
import { validateDocument } from '@/core/validator';
import { loadConfig } from '@/config/loader';

describe('Document Validation Integration', () => {
  it('should validate a complete document', async () => {
    const config = await loadConfig('./fixtures/basic/.shirushi.yml');
    const document = {
      path: 'docs/test.md',
      doc_id: 'PCE-SPEC-2025-0001-G',
      metadata: {
        title: 'Test',
        doc_type: 'spec',
        created_at: '2025-01-01',
      },
    };

    const results = await validateDocument(document, config, index);

    expect(results.every((r) => r.valid)).toBe(true);
  });
});
```

### Property-Based Tests

Use `fast-check` for property-based testing:

```typescript
// tests/unit/checksum.test.ts
import { describe, it } from 'vitest';
import fc from 'fast-check';
import { mod26AZ } from '@/dimensions/handlers/checksum';

describe('mod26AZ Property-Based Tests', () => {
  it('should always return single uppercase letter', () => {
    fc.assert(
      fc.property(fc.string(), (input) => {
        if (input.length === 0) return true; // Skip empty

        const result = mod26AZ(input);

        return (
          result.length === 1 &&
          result >= 'A' &&
          result <= 'Z'
        );
      })
    );
  });

  it('should be deterministic', () => {
    fc.assert(
      fc.property(fc.string(), (input) => {
        if (input.length === 0) return true;

        const result1 = mod26AZ(input);
        const result2 = mod26AZ(input);

        return result1 === result2;
      })
    );
  });
});
```

### E2E Tests

Test CLI commands end-to-end:

```typescript
// tests/e2e/cli.test.ts
import { describe, it, expect } from 'vitest';
import { execSync } from 'child_process';

describe('CLI E2E Tests', () => {
  it('should validate valid documents', () => {
    const result = execSync(
      'node dist/cli/index.js lint --config tests/fixtures/valid/.shirushi.yml',
      { encoding: 'utf-8' }
    );

    expect(result).toContain('✓ All documents valid');
  });

  it('should fail on invalid documents', () => {
    expect(() => {
      execSync(
        'node dist/cli/index.js lint --config tests/fixtures/invalid/.shirushi.yml',
        { encoding: 'utf-8' }
      );
    }).toThrow();
  });
});
```

---

## Code Style

### TypeScript Guidelines

1. **Use Explicit Return Types for Public APIs**

```typescript
// Good
export function parseTemplate(template: string): string[] {
  // ...
}

// Avoid (implicit return type)
export function parseTemplate(template: string) {
  // ...
}
```

2. **Use `const` for Immutable Values**

```typescript
// Good
const config = await loadConfig();

// Avoid
let config = await loadConfig();
```

3. **Prefer `type` over `interface` for Unions**

```typescript
// Good
export type Dimension = EnumDimension | YearDimension | SerialDimension;

// Avoid
export interface Dimension {
  // Can't represent unions
}
```

4. **Use Discriminated Unions**

```typescript
// Good
type Result =
  | { valid: true }
  | { valid: false; error: string };

// Avoid
type Result = {
  valid: boolean;
  error?: string; // Might be undefined
};
```

### Naming Conventions

- **Files**: `kebab-case.ts` (e.g., `enum-from-doc-type.ts`)
- **Classes**: `PascalCase` (e.g., `DimensionHandler`)
- **Functions**: `camelCase` (e.g., `validateDocument`)
- **Constants**: `UPPER_SNAKE_CASE` (e.g., `DEFAULT_INDEX_FILE`)
- **Types/Interfaces**: `PascalCase` (e.g., `ValidationResult`)

### Comments

Use JSDoc for public APIs:

```typescript
/**
 * Validates a document against its configuration.
 *
 * @param document - The document to validate
 * @param config - The Shirushi configuration
 * @param index - The document index
 * @returns Array of validation results (empty if all valid)
 *
 * @example
 * ```typescript
 * const results = await validateDocument(doc, config, index);
 * if (results.some(r => !r.valid)) {
 *   console.error('Validation failed');
 * }
 * ```
 */
export async function validateDocument(
  document: Document,
  config: ShirushiConfig,
  index: DocumentIndex
): Promise<ValidationResult[]> {
  // ...
}
```

---

## Contributing

### Workflow

1. **Fork** the repository
2. **Create** a feature branch (`git checkout -b feature/my-feature`)
3. **Write** tests for your changes
4. **Implement** your changes
5. **Ensure** all tests pass (`pnpm test`)
6. **Lint** your code (`pnpm lint`)
7. **Commit** with descriptive message
8. **Push** to your fork
9. **Create** a pull request

### Commit Messages

Follow conventional commits:

```
feat: add region dimension type
fix: correct checksum calculation for Unicode
docs: update developer guide with testing examples
test: add property-based tests for serial handler
refactor: extract common validation logic
chore: update dependencies
```

### Pull Request Guidelines

- Link to related issue (if exists)
- Describe what changed and why
- Include tests for new functionality
- Update documentation if needed
- Ensure CI passes

---

## Interface Design

CLI インターフェース、`.shirushi.yml` のスキーマ、ドキュメント/インデックスのデータ契約、そして内部モジュールの責務・フローは `api/interface-design.md` にまとめています。API/MCP など外部統合を検討する際はまずこの文書を参照し、必要な拡張ポイントを共有してください。

## Internal Design

さらに深いコンポーネント責務や `CoreContext` の構造、lint/assign の詳細シーケンス、永続化やエラー伝播の流れは `api/internal-design.md` に整理しました。モジュール改修や新トランスポート/API を実装する際はこちらを参照してください。

## Additional Resources

- [Architecture Decision Records](adr/) - Design decisions
- [User Guide](user-guide.md) - End-user documentation
- [Specification](../specifications.md) - Original specification (Japanese)
- [TypeScript Handbook](https://www.typescriptlang.org/docs/handbook/)
- [Zod Documentation](https://zod.dev/)
- [Vitest Documentation](https://vitest.dev/)
