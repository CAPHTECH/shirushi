---
doc_id: SHI-ADR-2025-0006-K
title: "ADR-0006: No Gap Validation for Serial Numbers in v0.1"
version: "1.0.0"
status: Accepted
created_at: 2025-01-19
---

# ADR-0006: No Gap Validation for Serial Numbers in v0.1

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: validation, serial-numbers, scope

---

## Context

The `serial` dimension type generates sequential numbers within a scope:

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]
```

Example IDs with serials:
```
PCE-SPEC-2025-0001-A
PCE-SPEC-2025-0002-B
PCE-SPEC-2025-0003-C
```

The specification states:

> 連番の飛び（0001, 0005, 0100…）まで厳密に検査するかどうかは初期仕様では規定せず、実装や運用ポリシーに委ねる。
> (Whether to strictly check for gaps in serial numbers (0001, 0005, 0100...) is not specified in the initial spec, left to implementation and operational policy.)

We need to decide: should we validate that serials are **contiguous** (no gaps)?

## Decision

**Do NOT validate for gaps in serial numbers in v0.1.**

Validation will only check:
- ✅ Serial number is correct digit length (e.g., 4 digits)
- ✅ Serial number is within scope
- ✅ No duplicate serial numbers within the same scope
- ❌ No gaps in sequence (0001, 0002, 0003, ...)

Examples that will **pass** validation:

```
PCE-SPEC-2025-0001-A  ✓
PCE-SPEC-2025-0005-E  ✓  (Gap between 0001 and 0005 - OK)
PCE-SPEC-2025-0100-X  ✓  (Gap between 0005 and 0100 - OK)
```

Examples that will **fail** validation:

```
PCE-SPEC-2025-0001-A    ✓
PCE-SPEC-2025-0001-A    ✗  (Duplicate - FAIL)
PCE-SPEC-2025-001-B     ✗  (Wrong digit length - FAIL)
```

## Rationale

### Why Allow Gaps?

1. **Valid Use Cases for Gaps**

   - **Document Deletion**: A document is removed but we don't renumber everything
   - **Draft Documents**: Assigned IDs but never published
   - **Migration**: Existing numbering system has gaps
   - **Parallel Development**: Multiple branches creating IDs simultaneously
   - **Reserved Numbers**: Some numbers reserved for future use

2. **Operational Flexibility**

   - Strict contiguity is overly rigid
   - Teams may have legitimate reasons for gaps
   - Renumbering is expensive and error-prone
   - Gap detection would block valid workflows

3. **Complexity vs. Value**

   - Gap detection adds significant complexity
   - Requires tracking "expected next number"
   - Ambiguous: Is gap an error or intentional?
   - Limited actual value (gaps don't break anything)

4. **Specification Alignment**

   - Spec explicitly leaves this to implementation
   - Indicates it's not critical for v0.1

### What Gaps Don't Break

Gaps in serials do **not** affect:
- ID uniqueness (still guaranteed)
- Checksum validation (still works)
- Index consistency (still validated)
- Document integrity (still maintained)

### What Problem Does Contiguity Solve?

Contiguity primarily serves **aesthetic** purposes:
- "Clean" numbering
- Easy mental model ("we have 10 documents numbered 0001-0010")

These are nice-to-haves, not critical for v0.1.

## Alternatives Considered

### 1. Strict Contiguity Validation (No Gaps Allowed)

Require serials to be contiguous: 0001, 0002, 0003, ...

**Pros**:
- Clean, predictable numbering
- Easy to understand "how many documents we have"
- Might catch some errors (e.g., typo 0105 instead of 0015)

**Cons**:
- Blocks valid workflows (deletion, drafts, migration)
- Forces renumbering when documents are removed
- Makes parallel development difficult
- Rigid and inflexible
- Adds significant complexity

**Rejected**: Too restrictive for real-world usage.

### 2. Gap Validation with Warnings (Not Errors)

Detect gaps but only warn, don't fail validation.

**Pros**:
- Informative (users know about gaps)
- Doesn't block workflows
- Flexible

**Cons**:
- Warnings often ignored
- Ambiguous: when is a gap intentional vs. error?
- Still requires gap detection logic
- Clutters output with non-actionable warnings

**Rejected**: Warnings without clear action are noise.

### 3. Configurable Gap Validation

Let users choose via configuration:

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]
  allow_gaps: true  # or false
```

**Pros**:
- Maximum flexibility
- Teams can choose their policy

**Cons**:
- More configuration complexity
- Most teams wouldn't know what to choose
- Defer decision to user (analysis paralysis)
- Adds implementation complexity

**Rejected**: Premature configuration. Can add in v0.2 if needed.

### 4. Strict Mode Flag

Default allows gaps, but `--strict` flag validates contiguity:

```bash
shirushi lint --strict
```

**Pros**:
- Default is permissive
- Opt-in strictness for teams that want it
- Clear separation

**Cons**:
- Still need to implement gap detection
- Adds complexity to v0.1
- Can defer to v0.2

**Deferred**: Good idea for future, but not v0.1.

## Consequences

### Positive

- **Flexibility**: Support real-world workflows (deletion, drafts, etc.)
- **Simplicity**: Reduced validation complexity
- **Faster Development**: Less code to write and test
- **No False Positives**: Won't block valid documents
- **Future-Proof**: Can add stricter validation later if needed

### Negative

- **No Gap Detection**: Won't catch accidental large gaps (e.g., 0001 → 0999)
- **Aesthetic**: Numbering might look "messy"
- **Manual Review**: Teams that want contiguity must check manually

### Neutral

- Standard approach (most ID systems allow gaps)
- Align with real-world practices (GitHub issues, JIRA tickets have gaps)

## Implementation Notes

### Validation Logic

```typescript
function validateSerial(
  value: string,
  dimension: SerialDimension,
  context: ValidationContext
): ValidationResult {
  // 1. Check digit length
  if (value.length !== dimension.digits) {
    return {
      error: 'INVALID_SERIAL_FORMAT',
      message: `Serial must be ${dimension.digits} digits, got ${value.length}`,
    };
  }

  // 2. Check it's numeric
  if (!/^\d+$/.test(value)) {
    return {
      error: 'INVALID_SERIAL_FORMAT',
      message: `Serial must be numeric, got ${value}`,
    };
  }

  // 3. Check for duplicates within scope
  const scopeKey = getScopeKey(dimension.scope, context);
  const existingSerials = getDocumentsInScope(scopeKey, context.index);

  if (existingSerials.includes(value)) {
    return {
      error: 'DUPLICATE_SERIAL',
      message: `Serial ${value} already exists in scope ${scopeKey}`,
    };
  }

  // ✅ NO GAP VALIDATION
  // We do NOT check if serials are contiguous

  return { valid: true };
}
```

### What We Do Check

```typescript
// ✅ Length check
"001"  → FAIL (should be 4 digits: "0001")
"0001" → PASS

// ✅ Numeric check
"000A" → FAIL (not numeric)
"0001" → PASS

// ✅ Duplicate check
["0001", "0001"] → FAIL (duplicate)
["0001", "0005"] → PASS (gap OK, no duplicate)

// ❌ Contiguity NOT checked
["0001", "0005", "0100"] → PASS (gaps allowed)
```

## Future Enhancements

For v0.2 or later, we could add:

### 1. Optional Strict Mode

```bash
shirushi lint --strict-serials
```

Validates contiguity when explicitly requested.

### 2. Gap Reporting (Informational)

```bash
shirushi scan --show-gaps
```

Output:
```
PCE-SPEC-2025: 0001, 0005, 0100 (gaps: 0002-0004, 0006-0099)
```

Informational only, not an error.

### 3. Configuration Option

```yaml
SER4:
  type: serial
  digits: 4
  scope: ["COMP", "KIND", "YEAR4"]
  validation:
    allow_gaps: false  # Opt-in to strict validation
```

## Related Decisions

None (standalone decision)

## Notes

### Real-World Examples

Many real-world ID systems allow gaps:

- **GitHub Issues**: #1, #5, #100 (deleted issues create gaps)
- **RFCs**: RFC 1, RFC 5, RFC 100 (gaps are common)
- **JIRA Tickets**: PROJ-1, PROJ-5, PROJ-100 (cancelled tickets)
- **Database Auto-Increment**: 1, 5, 100 (deleted rows)

Gaps are normal and expected in mature ID systems.

### Quote from Spec

> 連番の飛び（0001, 0005, 0100…）まで厳密に検査するかどうかは初期仕様では規定せず、実装や運用ポリシーに委ねる。

This gives us explicit permission to defer gap validation. The spec authors recognized this is a policy decision, not a technical requirement.
