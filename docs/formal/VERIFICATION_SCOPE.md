---
doc_id: SHI-FORMAL-2025-0006
title: Formal Verification Scope and Assumptions
version: "0.1.0"
status: Draft
created_at: 2025-11-29
---

# Formal Verification Scope and Assumptions

This document explicitly defines what is verified by the formal specifications, what assumptions are made, and what is intentionally out of scope.

## 1. Verification Coverage

### 1.1 Safety Properties (Verified)

| Property ID | Property Name | Specification | Status |
|-------------|---------------|---------------|--------|
| S1 | ID Uniqueness | `shirushi.als: uniqueDocIDs` | Verified (UNSAT) |
| S2 | Index Consistency | `shirushi.als: docIndexConsistency` | Verified (UNSAT) |
| S3 | Checksum Integrity | `shirushi.als: validChecksum` | Verified (UNSAT) |
| S4 | Serial Scope Isolation | `shirushi.als: uniqueSerialsInScope` | Verified (UNSAT) |
| S5 | ID Immutability | `shirushi.als: idImmutabilityEnforced` | Verified (UNSAT) |
| S6 | Type Correctness | `shirushi.tla: TypeInvariant` | Verified (TLC) |
| S7 | Patch Atomicity | `shirushi.tla: PatchAtomicityInvariant` | Verified (TLC) |
| S8 | Lock Mutual Exclusion | `ShirushiPar.tla: MutexInvariant` | Verified (model) |
| S9 | Parallel Limit | `ShirushiPar.tla: ParallelLimitRespected` | Verified (model) |

### 1.2 Liveness Properties (Verified with Fairness)

| Property ID | Property Name | Specification | Fairness Assumption |
|-------------|---------------|---------------|---------------------|
| L1 | Termination | `ShirushiSeq.tla: Termination` | WF_vars(Next) |
| L2 | Progress | `ShirushiSeq.tla: Progress` | WF_vars(Next) |
| L3 | Lock Release | `ShirushiPar.tla: LockEventuallyReleased` | WF_vars(WorkerReleaseLock) |

### 1.3 Structural Properties (Verified)

| Property ID | Property Name | Specification | Status |
|-------------|---------------|---------------|--------|
| A1 | Architecture Layers | `shirushi.als: ArchitectureLayersRespected` | Verified (UNSAT) |
| A2 | No Cyclic Dependencies | `shirushi.als: NoCyclesInDependencies` | Verified (fact) |
| A3 | Config Soundness | `ShirushiBoundary.als: ConfigSoundness` | Verified (UNSAT) |

---

## 2. Explicit Assumptions

### 2.1 Environmental Assumptions

| ID | Assumption | Justification | Risk if Violated |
|----|------------|---------------|------------------|
| E1 | File system is consistent (no concurrent modification during read) | OS-level guarantee | Corrupted reads, race conditions |
| E2 | Git repository is in valid state | Git guarantees | Parse errors, invalid refs |
| E3 | Sufficient memory for document set | Operational constraint | OOM, incomplete validation |
| E4 | UTF-8 encoding for all documents | Project convention | Parsing failures |

### 2.2 Configuration Assumptions

| ID | Assumption | Where Enforced | Default Value |
|----|------------|----------------|---------------|
| C1 | `MaxSerialPerScope > 0` | Zod schema | 9999 |
| C2 | `forbid_id_change` is boolean | Zod schema | `true` |
| C3 | All dimension names in format are defined | Zod schema refinement | N/A |
| C4 | Checksum dimensions don't reference themselves | Zod schema refinement | N/A |

### 2.3 Behavioral Assumptions

| ID | Assumption | Specification | Implementation Responsibility |
|----|------------|---------------|-------------------------------|
| B1 | Handlers are pure functions (no side effects) | `ShirushiBoundary.als: HandlersArePure` | Code review, unit tests |
| B2 | Parse operations are deterministic | Implicit | Parser implementation |
| B3 | Checksum computation is deterministic | `shirushi.als: checksumLetter` | `mod26AZ()` implementation |
| B4 | Serial counter starts at 0 for new scopes | `shirushi.tla: Init` | `serial.ts` handler |

### 2.4 Fairness Assumptions (for Liveness)

| ID | Assumption | Required For | Realistic? |
|----|------------|--------------|------------|
| F1 | Every enabled action eventually executes | Termination | Yes (single-threaded CLI) |
| F2 | Workers eventually release locks | Lock liveness | Yes (with timeout) |
| F3 | No infinite loop in handlers | Progress | Code review responsibility |

---

## 3. Out of Scope

### 3.1 Not Modeled

| Item | Reason | Risk Mitigation |
|------|--------|-----------------|
| File I/O errors (disk full, permission denied) | Infrastructure concern | Error handling in implementation |
| Network failures (for future remote index) | Not in v0.1 scope | Retry logic when implemented |
| Process crashes during two-phase assign | Requires recovery protocol | Manual re-run; idempotent design |
| Memory corruption | Hardware failure | OS/runtime responsibility |
| Malicious input (attack vectors) | Security audit scope | Input sanitization |

### 3.2 Simplified in Model

| Item | Simplification | Real Behavior |
|------|----------------|---------------|
| Checksum algorithm | Fixed mapping table | Actual mod26 computation |
| Year extraction | Fixed "2025" | `new Date().getFullYear()` or metadata |
| Serial formatting | Fixed "0001", "0002" | Zero-padded number generation |
| Glob matching | Category-based | Full glob syntax |
| Error messages | Error codes only | Localized messages with context |

### 3.3 Deferred to Future Versions

| Item | Target Version | Reason |
|------|----------------|--------|
| Assign command implementation | v0.2 | ADR-0005 |
| Distributed index synchronization | v0.3+ | Complexity |
| Plugin/extension system | v0.4+ | API stability first |
| Performance optimization | v0.2+ | Correctness first |

---

## 4. Known Limitations

### 4.1 Model Checking Bounds

| Specification | Bound | Implication |
|---------------|-------|-------------|
| `shirushi.als` | `for 5 but 3 Document, 3 DocID` | Only small configurations checked |
| `shirushi.tla` | `MaxDocs = 3, MaxHistory = 10` | State space limited |
| `ShirushiPar.tla` | `Workers = {w1, w2}, MaxParallel = 2` | Only 2-worker scenarios |

**Mitigation**: Property-based testing with larger inputs in implementation tests.

### 4.2 Abstraction Gaps

| Gap | Formal Model | Real Implementation |
|-----|--------------|---------------------|
| String operations | Abstract `String` sig | Full UTF-8 handling |
| Path matching | Category membership | Glob/regex patterns |
| Time handling | `YearSource` enum | `Date` object, timezones |
| Error reporting | `ErrorCode` enum | Structured error with location |

### 4.3 Unverified Composition

| Composition | Status | Notes |
|-------------|--------|-------|
| Alloy + TLA+ consistency | Manually reviewed | Same invariant names, different representations |
| Spec + Implementation | Unit tests | No formal refinement proof |
| Sequential + Parallel models | Assertion equivalence | Both verify same safety properties |

---

## 5. Verification Results Summary

### 5.1 Alloy (`shirushi.als`)

```
Verification Date: 2025-11-29
Tool: Alloy 6.2.0

00. check ArchitectureLayersRespected     UNSAT ✓
01. check noDuplicatesWhenValid           UNSAT ✓
02. check documentPrecedenceDetected      UNSAT ✓
03. check checksumDetectsTampering        UNSAT ✓
04. check serialScopeIsolation            UNSAT ✓
05. check idImmutabilityEnforced          UNSAT ✓
```

### 5.2 TLA+ (`shirushi.tla`)

```
Verification Date: 2025-11-29
Tool: TLC 2.20

States Generated: 271,247
Distinct States: 68,011
Depth: 7
Result: No error has been found ✓
```

### 5.3 Boundary Comparison (`ShirushiBoundary.als`)

```
Verification Date: 2025-11-29
Tool: Alloy 6.2.0

00. run runProfileA                       SAT ✓
01. run runProfileC                       SAT ✓
02. run runProfilesDiffer                 SAT ✓
03. check ProfileA_MaintainsInvariants    UNSAT ✓ (after fix)
04. check ProfileC_MaintainsInvariants    UNSAT ✓ (after fix)
05. check ConfigSoundness_Independent     UNSAT ✓
```

---

## 6. Recommendations

### 6.1 Before Implementation

1. Review this document with implementation team
2. Ensure all assumptions are documented in code comments
3. Create unit tests for each safety property

### 6.2 During Implementation

1. Reference `SPEC_IMPL_MAPPING.md` for type/function naming
2. Add `@invariant` comments linking to formal properties
3. Implement property-based tests for invariants

### 6.3 After Implementation

1. Run mutation testing to verify test quality
2. Compare implementation behavior with TLA+ traces
3. Update formal specs if implementation diverges

---

## 7. Change Log

| Version | Date | Changes |
|---------|------|---------|
| 0.1.0 | 2025-11-29 | Initial scope definition |

---

## References

- `shirushi.als` - Alloy structural specification
- `shirushi.tla` - TLA+ behavioral specification
- `ShirushiSeq.tla` - Sequential validation model
- `ShirushiPar.tla` - Parallel validation model
- `ShirushiBoundary.als` - Architecture boundary comparison
- ADR documents in `docs/adr/`
