---
doc_id: SHI-ADR-2025-0004
title: "ADR-0004: Use Simple mod26AZ Checksum Algorithm"
version: "1.0.0"
status: Accepted
created_at: 2025-01-19
---

# ADR-0004: Use Simple mod26AZ Checksum Algorithm

**Status**: Accepted

**Date**: 2025-01-19

**Deciders**: Architecture Team

**Tags**: checksum, validation, security

---

## Context

Shirushi needs a checksum dimension to detect accidental modifications to document IDs. The specification mentions:

> **`algo`**:
> 現バージョンでは最低限 `"mod26AZ"` をサポートする。
> 対象文字列を適当な方式で数値列に変換し、合計値を 26 で割った余りを A–Z に対応させるシンプルな方式。

The checksum serves to:
1. Detect typos or accidental ID modifications
2. Provide a quick validation check
3. Help prevent manual ID manipulation

We need to define the specific algorithm for v0.1.

## Decision

Implement **mod26AZ** checksum algorithm as follows:

```typescript
function mod26AZ(input: string): string {
  // Sum ASCII values of all characters
  const sum = input
    .split('')
    .reduce((acc, char) => acc + char.charCodeAt(0), 0);

  // Modulo 26, map to A-Z
  const checksumValue = sum % 26;
  return String.fromCharCode(65 + checksumValue); // 65 = 'A'
}
```

**Example**:
```typescript
mod26AZ('PCE-SPEC-2025-0001')
// 'P'(80) + 'C'(67) + 'E'(69) + '-'(45) + ... = sum
// sum % 26 = remainder
// 'A' + remainder = checksum character
```

**Characteristics**:
- Deterministic
- ASCII-only input support
- Single character output (A-Z)
- Simple to implement and verify
- Not cryptographically secure (by design)

## Rationale

### Purpose of Checksum

The checksum is **not** for:
- Security (preventing malicious tampering)
- Cryptographic integrity
- Collision resistance

The checksum **is** for:
- Catching accidental typos (e.g., "PCE-SPEC-2025-0001-**X**" when it should be "**G**")
- Detecting AI/LLM modifications during document editing
- Quick validation without complex lookups

### Why This Simple Algorithm?

1. **Sufficient for Purpose**: Detects most accidental changes
2. **Easy to Understand**: Users can manually verify if needed
3. **Fast to Compute**: No performance concerns
4. **Deterministic**: Same input always produces same output
5. **Single Character**: Keeps IDs compact

## Alternatives Considered

### 1. CRC32 (Last Character)

```typescript
import crc32 from 'crc-32';
const checksum = crc32.str(input) % 26;
```

**Pros**:
- Better error detection
- Industry standard

**Cons**:
- Overkill for the use case
- External dependency
- More complex to understand
- Not significantly better for typo detection

**Rejected**: Too complex for the stated purpose.

### 2. Luhn Algorithm

Used in credit card numbers.

**Pros**:
- Designed for detecting typos
- Catches transposition errors

**Cons**:
- Only works with numeric inputs
- Our IDs have letters
- Would need adaptation

**Rejected**: Not suitable for alphanumeric IDs.

### 3. Simple XOR

```typescript
const checksum = input
  .split('')
  .reduce((acc, char) => acc ^ char.charCodeAt(0), 0) % 26;
```

**Pros**:
- Very fast
- Simple

**Cons**:
- Order-independent (permutations give same checksum)
- "AB" and "BA" would have same checksum

**Rejected**: Weaker error detection than sum.

### 4. Cryptographic Hash (MD5, SHA-1)

```typescript
const hash = crypto.createHash('md5').update(input).digest('hex');
const checksum = parseInt(hash[0], 16) % 26;
```

**Pros**:
- Strong integrity
- Collision resistance

**Cons**:
- Massive overkill
- Slower
- Requires crypto library
- Against stated goal of "simple"

**Rejected**: Violates simplicity requirement.

## Consequences

### Positive

- **Simplicity**: Easy to implement, test, and understand
- **No Dependencies**: Pure JavaScript, no external libraries
- **Fast**: O(n) where n = input length, negligible cost
- **Transparent**: Users can manually verify if needed
- **Deterministic**: Reliable and predictable

### Negative

- **Weak Against Intentional Tampering**: Not secure (but not the goal)
- **Collision Possible**: Different inputs can produce same checksum (acceptable)
- **No Transposition Detection**: Swapping characters might not be caught
- **ASCII Only**: Unicode characters would need handling (defer to future)

### Neutral

- For v0.1, this is sufficient
- Can be enhanced in future versions if needed
- Users who need stronger validation can implement custom dimension types later

## Implementation Notes

### Handling Edge Cases

```typescript
function mod26AZ(input: string): string {
  // Input validation
  if (input.length === 0) {
    throw new Error('Cannot compute checksum of empty string');
  }

  // ASCII-only for v0.1
  if (!/^[\x00-\x7F]*$/.test(input)) {
    throw new Error('mod26AZ only supports ASCII characters in v0.1');
  }

  const sum = input
    .split('')
    .reduce((acc, char) => acc + char.charCodeAt(0), 0);

  const checksumValue = sum % 26;
  return String.fromCharCode(65 + checksumValue);
}
```

### Usage in Configuration

```yaml
CHK1:
  type: checksum
  algo: "mod26AZ"
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

### Validation Example

```typescript
function validateChecksum(
  docId: string,
  config: ChecksumDimension
): ValidationResult {
  // Extract parts specified in 'of'
  const parts = config.of.map(dim => extractDimensionValue(docId, dim));
  const input = parts.join('');

  // Compute expected checksum
  const expected = mod26AZ(input);

  // Extract actual checksum from doc_id
  const actual = extractDimensionValue(docId, 'CHK1');

  if (actual !== expected) {
    return {
      error: 'INVALID_ID_CHECKSUM',
      message: `Checksum mismatch: expected ${expected}, got ${actual}`,
      expected,
      actual,
    };
  }

  return { valid: true };
}
```

## Future Enhancements

Potential improvements for future versions:

1. **Additional Algorithms**: Support CRC32, SHA-1, custom algorithms
2. **Multi-character Checksums**: Allow 2-3 character checksums for stronger detection
3. **Unicode Support**: Handle Unicode properly
4. **Configurable**: Allow users to specify their own checksum function

```yaml
# Future possibility
CHK2:
  type: checksum
  algo: "crc32-base26"
  digits: 2  # AA-ZZ
  of: ["COMP", "KIND", "YEAR4", "SER4"]
```

## Related Decisions

None (standalone decision)

## Notes

This decision prioritizes **simplicity and transparency** over **strength**. The checksum is a helpful safeguard, not a security mechanism.

References:
- [Checksum on Wikipedia](https://en.wikipedia.org/wiki/Checksum)
- [Error Detection Codes](https://en.wikipedia.org/wiki/Error_detection_and_correction)
