---
doc_id: SHI-ADR-2025-0001
title: ADR-0001: Use Discriminated Unions for Dimension Types
version: "1.0.0"
status: Accepted
created_at: 2025-01-19
---

# ADR-0001: Use Discriminated Unions for Dimension Types

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: typescript, type-safety, extensibility

---

## Context

Shirushi needs to support multiple dimension types (enum, enum_from_doc_type, year, serial, checksum) with different properties and validation logic. We need a type-safe way to represent these different dimension types while:

1. Ensuring compile-time type safety
2. Allowing for future extensibility
3. Enabling exhaustive checking in switch statements
4. Maintaining clear separation of concerns

The specification states: "今後の拡張として、新たな部品型を追加する余地を残す" (leave room for adding new dimension types in the future).

## Decision

We will use TypeScript discriminated unions for dimension type definitions:

```typescript
type Dimension =
  | EnumDimension
  | EnumFromDocTypeDimension
  | YearDimension
  | SerialDimension
  | ChecksumDimension;

interface BaseDimension {
  type: string;
}

interface EnumDimension extends BaseDimension {
  type: 'enum';
  values: string[];
  select?: { by_path: Array<{ pattern: string; value: string }> };
}

interface SerialDimension extends BaseDimension {
  type: 'serial';
  digits: number;
  scope: string[];
}

// ... etc
```

Each dimension type will have a corresponding handler implementing a common interface:

```typescript
interface DimensionHandler<T extends Dimension> {
  validate(value: string, dimension: T, context: ValidationContext): ValidationResult;
  generate(dimension: T, context: GenerationContext): string;
  toPattern(dimension: T): string; // For regex generation
}
```

## Alternatives Considered

### 1. Class Hierarchy with Inheritance

```typescript
abstract class Dimension {
  abstract validate(): ValidationResult;
}

class EnumDimension extends Dimension {
  // ...
}
```

**Rejected because**:
- More verbose
- Less idiomatic in TypeScript
- Harder to serialize/deserialize from YAML
- Couples data and behavior

### 2. Generic Objects with Runtime Type Checking

```typescript
interface Dimension {
  type: string;
  [key: string]: any;
}
```

**Rejected because**:
- No compile-time type safety
- Loses autocomplete support
- Requires extensive runtime validation
- Error-prone

### 3. Separate Type per Dimension

```typescript
// No union type, just separate interfaces
```

**Rejected because**:
- Can't have a collection of mixed dimension types
- No exhaustive checking
- Harder to work with in validation logic

## Consequences

### Positive

- **Type Safety**: TypeScript compiler ensures all dimension types are handled
- **Exhaustive Checking**: Switch statements on `dimension.type` are exhaustively checked
- **Autocomplete**: IDE provides accurate autocomplete for dimension properties
- **Serialization**: Works well with Zod for runtime validation and type inference
- **Future-Proof**: Easy to add new dimension types by extending the union

### Negative

- **Boilerplate**: Each new dimension type requires interface definition
- **Learning Curve**: Team members need to understand discriminated unions
- **Zod Complexity**: Discriminated unions require `z.discriminatedUnion()` which is more complex

### Neutral

- Standard TypeScript pattern, widely used in the ecosystem
- Aligns with functional programming principles (data and behavior separation)

## Related Decisions

- ADR-0002: Use Zod for Configuration Validation (depends on this decision)

## Notes

References:
- [TypeScript Handbook: Discriminated Unions](https://www.typescriptlang.org/docs/handbook/2/narrowing.html#discriminated-unions)
- [Zod Discriminated Unions](https://zod.dev/?id=discriminated-unions)
