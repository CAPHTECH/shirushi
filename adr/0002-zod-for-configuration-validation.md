# ADR-0002: Use Zod for Configuration Validation

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: validation, configuration, type-safety

---

## Context

Shirushi requires robust validation of `.shirushi.yml` configuration files. The configuration structure is complex with:

- Nested objects (dimensions, rules)
- Multiple dimension types with different schemas
- Cross-field validation (e.g., id_format must reference defined dimensions)
- Need for both runtime validation and TypeScript type inference

We need a solution that provides:
1. Runtime validation with clear error messages
2. TypeScript type inference from schema
3. Support for complex validation rules
4. Good developer experience

## Decision

We will use **Zod** as our schema validation library for configuration files.

Example usage:

```typescript
import { z } from 'zod';

// Define schemas
const EnumDimensionSchema = z.object({
  type: z.literal('enum'),
  values: z.array(z.string()).min(1),
  select: z.object({
    by_path: z.array(z.object({
      pattern: z.string(),
      value: z.string(),
    })),
  }).optional(),
});

const DimensionSchema = z.discriminatedUnion('type', [
  EnumDimensionSchema,
  EnumFromDocTypeDimensionSchema,
  YearDimensionSchema,
  SerialDimensionSchema,
  ChecksumDimensionSchema,
]);

const ConfigSchema = z.object({
  doc_globs: z.array(z.string()).min(1),
  id_format: z.string(),
  dimensions: z.record(z.string(), DimensionSchema),
  index_file: z.string().default('docs/doc_index.yaml'),
  forbid_id_change: z.boolean().default(true),
  allow_missing_id_in_new_files: z.boolean().default(false),
});

// Infer TypeScript type from schema
type ShirushiConfig = z.infer<typeof ConfigSchema>;

// Use for validation
const config = ConfigSchema.parse(yamlData);
```

## Alternatives Considered

### 1. JSON Schema with ajv

```typescript
import Ajv from 'ajv';
const ajv = new Ajv();
const validate = ajv.compile(jsonSchema);
```

**Pros**:
- Industry standard
- Wide tooling support
- Can generate schemas from TypeScript

**Cons**:
- Separate type definitions required (no type inference)
- Less TypeScript-friendly
- More verbose error messages
- Harder to compose schemas

### 2. io-ts

```typescript
import * as t from 'io-ts';
const ConfigCodec = t.type({
  doc_globs: t.array(t.string),
  // ...
});
```

**Pros**:
- Strong type safety
- Functional programming approach
- Bidirectional encoding/decoding

**Cons**:
- Steeper learning curve
- More verbose syntax
- Smaller community than Zod
- Less intuitive error messages

### 3. Class-validator with class-transformer

```typescript
import { IsString, IsArray } from 'class-validator';
class ShirushiConfig {
  @IsArray()
  @IsString({ each: true })
  doc_globs: string[];
}
```

**Pros**:
- Decorator-based (familiar to Angular/NestJS developers)
- Good class-based approach

**Cons**:
- Requires classes (not plain objects)
- Decorator overhead
- Not ideal for YAML parsing
- No schema composition

### 4. Manual Validation

```typescript
function validateConfig(config: unknown): ShirushiConfig {
  if (!config || typeof config !== 'object') {
    throw new Error('Invalid config');
  }
  // ... manual validation
}
```

**Pros**:
- Full control
- No dependencies

**Cons**:
- Verbose and error-prone
- Hard to maintain
- Poor error messages
- No automatic type inference

## Decision Rationale

Zod was chosen because:

1. **Type Inference**: Automatically generates TypeScript types from schemas
2. **Developer Experience**: Intuitive, TypeScript-first API
3. **Error Messages**: Clear, actionable error messages
4. **Composition**: Easy to compose and reuse schemas
5. **Discriminated Unions**: First-class support (works with ADR-0001)
6. **Refinements**: Custom validation logic with `.refine()`
7. **Transforms**: Can transform data during parsing
8. **Community**: Large, active community and good documentation

## Consequences

### Positive

- **Type Safety**: Single source of truth for both runtime validation and TypeScript types
- **Maintainability**: Schema changes automatically update TypeScript types
- **Error Reporting**: Users get clear, helpful error messages for invalid configs
- **Validation Logic**: Complex cross-field validation with `.refine()` and `.superRefine()`
- **Default Values**: Built-in support for default values
- **Testing**: Easy to test schemas in isolation

### Negative

- **Bundle Size**: Zod adds ~50KB to bundle (acceptable for CLI tool)
- **Learning Curve**: Team needs to learn Zod API
- **Performance**: Slightly slower than manual validation (negligible for config parsing)

### Neutral

- Zod is becoming a de facto standard in TypeScript ecosystem
- Well-maintained with frequent updates

## Implementation Notes

### Custom Validation Example

```typescript
const ConfigSchema = z.object({
  id_format: z.string(),
  dimensions: z.record(DimensionSchema),
}).refine((config) => {
  // Validate that id_format only references defined dimensions
  const placeholders = extractPlaceholders(config.id_format);
  const dimensionNames = Object.keys(config.dimensions);

  return placeholders.every(p => dimensionNames.includes(p));
}, {
  message: 'id_format references undefined dimensions',
  path: ['id_format'],
});
```

### Error Handling

```typescript
try {
  const config = ConfigSchema.parse(yamlData);
} catch (error) {
  if (error instanceof z.ZodError) {
    // Format errors for user
    const messages = error.errors.map(err =>
      `${err.path.join('.')}: ${err.message}`
    );
    throw new ConfigError(messages.join('\n'));
  }
  throw error;
}
```

## Related Decisions

- ADR-0001: Use Discriminated Unions for Dimension Types (complementary)

## Notes

References:
- [Zod Documentation](https://zod.dev/)
- [Zod GitHub Repository](https://github.com/colinhacks/zod)
- Comparison: [TypeScript Schema Validation Libraries](https://github.com/runtypes/runtypes/wiki/Comparison-of-Runtime-Type-Libraries)
