# Shirushi Formal Verification Strategy

## Overview

This document explains the verification approach for Shirushi, combining formal methods (Alloy/TLA+) with property-based testing to achieve comprehensive correctness guarantees.

## Verification Layers

### Layer 1: Alloy - Structural Invariants

**What Alloy verifies:**
- High-level system invariants (uniqueness, consistency)
- Dimension type system correctness
- Index-document relationships
- Configuration well-formedness
- Error detection logic completeness

**What Alloy does NOT verify:**
- String parsing implementation (`id_format` → regex)
- Checksum algorithm implementation (mod26AZ)
- File I/O correctness
- Git operations

**Abstraction strategy:**
- `parseDocID`, `computeChecksum`, and other string-manipulation functions are **axiomatically constrained** but not fully implemented
- Axioms capture essential properties (determinism, success conditions) without implementation details
- This is acceptable because:
  1. Alloy's string support is limited (no regex, no arithmetic on chars)
  2. Full implementation would duplicate TypeScript code
  3. Property-based tests provide rigorous verification of these components

**Trade-off:**
- **Benefit**: Fast model checking, focus on high-level correctness
- **Cost**: Implementation bugs in parse/checksum won't be caught by Alloy
- **Mitigation**: Layer 3 (property-based tests) specifically targets these functions

### Layer 2: TLA+ - Temporal Properties

**What TLA+ verifies:**
- State transition safety (`assign` operation)
- Immutability properties across time
- Concurrent operation correctness (if applicable in future)
- Liveness properties (e.g., "assign eventually succeeds for valid input")

**Focus areas:**
- `lint` is truly read-only (no state mutation)
- `assign` preserves all invariants
- Git `--base` comparison correctly detects ID changes
- No race conditions in future concurrent implementations

### Layer 3: Property-Based Testing (fast-check)

**What property tests verify:**
- `parseDocID` implementation correctness
  - Property: Parse → unparse → parse is idempotent
  - Property: All valid IDs parse successfully
  - Property: Invalid IDs are rejected

- `computeChecksum` (mod26AZ) implementation
  - Property: Deterministic (same input → same output)
  - Property: Small input changes → different checksums (sensitivity)
  - Property: Distributes evenly across A-Z range

- Dimension validator implementations
  - Property: All enum values pass validation
  - Property: Serial numbers within digit bounds validate
  - Property: Year validators accept valid years, reject invalid

**Test strategy:**
```typescript
// Example property test
fc.assert(
  fc.property(arbitraryDocID(config), (docID) => {
    const parsed = parseDocID(docID, config.id_format);
    const reconstructed = reconstructID(parsed, config.id_format);
    expect(reconstructed).toBe(docID); // Round-trip property
  })
);
```

### Layer 4: Integration Tests

**What integration tests verify:**
- End-to-end CLI commands work correctly
- File I/O operations are correct
- Git operations integrate properly
- Error messages are user-friendly

## Coverage Map

| Component | Alloy | TLA+ | Property Tests | Integration Tests |
|-----------|-------|------|----------------|-------------------|
| ID uniqueness | ✓ | ✓ | ✓ | ✓ |
| Checksum correctness | Axiom | — | ✓✓✓ | ✓ |
| Parse correctness | Axiom | — | ✓✓✓ | ✓ |
| Immutability | ✓ | ✓✓✓ | ✓ | ✓ |
| Index consistency | ✓✓✓ | ✓ | ✓ | ✓ |
| Dimension validation | ✓ | — | ✓✓✓ | ✓ |
| CLI correctness | — | — | ✓ | ✓✓✓ |
| Git integration | ✓ | ✓✓ | ✓ | ✓✓✓ |

**Legend:**
- ✓ = Verified
- ✓✓✓ = Primary verification method
- Axiom = Axiomatically assumed
- — = Not applicable

## Verification Workflow

1. **Design phase**: Write Alloy model, check assertions
2. **Specification phase**: Write TLA+ spec, model check temporal properties
3. **Implementation phase**:
   - Implement TypeScript code
   - Write property-based tests for abstract functions
   - Ensure Alloy axioms match actual behavior
4. **Testing phase**:
   - Run property tests (100,000+ iterations)
   - Run integration tests
   - Run mutation tests on critical modules
5. **CI phase**: All layers run on every commit

## Known Limitations

### Alloy Limitations

**Issue**: `parseDocID` and `computeChecksum` are placeholders
- **Impact**: Alloy cannot verify that implementation matches specification
- **Mitigation**: Property tests provide 100K+ test cases with random inputs

**Issue**: String operations are abstracted
- **Impact**: Cannot verify regex correctness, string concatenation order
- **Mitigation**: Unit tests explicitly check edge cases (empty strings, special chars)

**Issue**: File I/O is not modeled
- **Impact**: Cannot verify that file reads/writes work correctly
- **Mitigation**: Integration tests with fixture files

### TLA+ Limitations

**Issue**: Git DAG structure is simplified to linear history
- **Impact**: Cannot verify behavior with complex branching/merging
- **Mitigation**: v0.1 scope only requires base-to-HEAD comparison (linear)

**Issue**: Concurrent operations not modeled (v0.1)
- **Impact**: Future concurrent `assign` operations may have race conditions
- **Mitigation**: v0.2 will extend TLA+ spec before implementing concurrency

## Assertion Coverage

### Alloy Assertions (see shirushi.als)

1. `noDuplicatesWhenValid`: Invariants prevent duplicate doc_ids
2. `documentPrecedenceDetected`: Document is source of truth
3. `checksumDetectsTampering`: Invalid checksums are caught
4. `serialScopeIsolation`: Scopes correctly isolate serial numbers
5. `idImmutabilityEnforced`: Changed IDs are detected

### TLA+ Assertions (see shirushi.tla)

1. `TypeInvariant`: All state variables have correct types
2. `SystemInvariant`: All Alloy invariants hold in all reachable states
3. `LintReadOnly`: Lint never modifies state
4. `AssignPreservesInvariants`: Assign maintains uniqueness and consistency
5. `ImmutabilityNeverViolated`: Existing doc_ids never change

## Maintenance

- **When adding new dimension type**:
  1. Add to Alloy model
  2. Add validator to property tests
  3. Run full verification suite

- **When changing ID format**:
  1. Update Alloy `id_format` constraints
  2. Update TLA+ state machine
  3. Regenerate property test arbitraries

- **When finding bugs**:
  1. Create failing test case
  2. Fix implementation
  3. Add regression test
  4. Check if formal model needs updating

## References

- [Alloy Documentation](https://alloytools.org/documentation.html)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [fast-check Documentation](https://fast-check.dev/)
- [Lightweight Formal Methods](https://www.hillelwayne.com/post/fms-for-the-working-dev/)
