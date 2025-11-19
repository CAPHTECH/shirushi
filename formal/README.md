# Shirushi Formal Specifications

This directory contains formal verification artifacts for the Shirushi document ID management system using **Alloy** and **TLA+**.

## Contents

- **`shirushi.als`** - Alloy structural specification (invariants and constraints)
- **`shirushi.tla`** - TLA+ temporal specification (state transitions and properties)
- **`shirushi.cfg`** - TLC model checker configuration
- **`VERIFICATION_STRATEGY.md`** - Comprehensive verification approach documentation

## Quick Start

### Prerequisites

#### Alloy Analyzer
- Download from: https://github.com/AlloyTools/org.alloytools.alloy/releases
- Requires Java 11+
- Recommended version: Alloy 6.1.0+

#### TLA+ Toolbox
- Download from: https://github.com/tlaplus/tlaplus/releases
- Includes TLC model checker
- Alternative: Use command-line `tla2tools.jar`

### Running Alloy

```bash
# Using Alloy Analyzer GUI
# 1. Open shirushi.als in Alloy Analyzer
# 2. Select "Execute" menu
# 3. Choose a command:
#    - "run validSystem" - find a valid state
#    - "run systemWithErrors" - find error states
#    - "check noDuplicatesWhenValid" - verify assertion

# Using command line (if available)
java -jar org.alloytools.alloy.dist.jar shirushi.als
```

Expected output:
- **Commands (run)**: Should find instances satisfying predicates
- **Assertions (check)**: Should show "No counterexample found" if valid

### Running TLA+ (TLC)

```bash
# Using TLA+ Toolbox
# 1. Create new spec from shirushi.tla
# 2. Create model with shirushi.cfg settings
# 3. Run TLC model checker
# 4. Check results tab for invariant violations

# Using command line
java -jar tla2tools.jar -config shirushi.cfg shirushi.tla

# With more workers (faster)
java -jar tla2tools.jar -workers 4 -config shirushi.cfg shirushi.tla
```

Expected output:
```
TLC2 Version ...
...
Model checking completed. No errors found.
States explored: XXXX
```

### Interpreting Results

#### Alloy

**No counterexample found** ✅
- Assertion is valid within the specified scope
- Example: `check noDuplicatesWhenValid for 5` verified for up to 5 entities

**Counterexample found** ❌
- Alloy found a case where the assertion fails
- Use the instance visualizer to understand the scenario
- Review the model or implementation

**Instance found** ℹ️
- For `run` commands, this shows an example satisfying the predicate
- Useful for understanding valid/invalid states

#### TLA+

**No errors** ✅
- All invariants held in all reachable states (up to `StateConstraint`)
- Temporal properties verified

**Invariant violated** ❌
- TLC found a state where an invariant doesn't hold
- Check error trace to see the sequence of actions leading to violation
- Example:
  ```
  Error: Invariant SystemInvariant is violated.
  The behavior up to this point is:
    State 1: ...
    State 2: ...
    State 3: <violation>
  ```

**Deadlock detected** ⚠️
- System reached a state with no enabled actions
- May indicate missing transitions or over-constrained model

## Verification Scope

### What is Verified

| Property | Alloy | TLA+ | Notes |
|----------|-------|------|-------|
| doc_id uniqueness | ✓ | ✓ | Checked for all documents |
| Index consistency | ✓ | ✓ | Document = source of truth |
| Checksum correctness | Axiom | Axiom | Implementation verified by property tests |
| Serial scope isolation | ✓ | ✓ | Different scopes can have same serial |
| Immutability enforcement | ✓ | ✓ | Existing IDs never change |
| Lint is read-only | ✓ | ✓ | No state modifications |
| Assign preserves invariants | — | ✓ | Temporal property |
| Well-founded dimensions | ✓ | — | No circular dependencies |

### What is NOT Verified

- **String parsing implementation** - verified via property-based tests (fast-check)
- **Checksum algorithm (mod26AZ)** - verified via property-based tests
- **File I/O operations** - tested via integration tests
- **Git operations** - tested via integration tests
- **CLI error messages** - manual/integration testing

See `VERIFICATION_STRATEGY.md` for complete coverage map.

## Customizing the Models

### Adding New Dimension Types

1. **Alloy**: Add new signature extending `Dimension`
   ```alloy
   sig RegionDimension extends Dimension {
     regions: some String
   }
   ```

2. **TLA+**: Update `Assign` action logic
   ```tla
   regionValue == (* logic to determine region *)
   ```

3. **Re-run verification** to ensure no invariant violations

### Changing ID Format

1. Update `id_format` in `.shirushi.yml`
2. Update `IDFormat` in `shirushi.als`
3. Update `Assign` action in `shirushi.tla`
4. Re-verify all assertions

### Adjusting Verification Scope

**Alloy**:
```alloy
// Increase scope for more thorough checking (slower)
check noDuplicatesWhenValid for 10 but 5 Document, 5 DocID

// Decrease scope for faster iteration
check noDuplicatesWhenValid for 3
```

**TLA+**:
```tla
\* In shirushi.tla
StateConstraint == Len(history) <= 20  (* Increase from 10 *)
```

## Troubleshooting

### Alloy

**Problem**: "Analysis incomplete - some types are empty"
- **Cause**: Over-constrained model with no valid instances
- **Fix**: Check constraints in signature facts, relax if needed

**Problem**: "Timeout after X seconds"
- **Cause**: Scope too large, complex constraints
- **Fix**: Reduce scope, add `StateConstraint` predicate

### TLA+

**Problem**: "TLCExt module not found"
- **Cause**: Community modules not installed
- **Fix**: Download from https://github.com/tlaplus/CommunityModules
- Or remove dependency and use manual implementations (see ScopeKey function)

**Problem**: "Out of memory error"
- **Cause**: State space too large
- **Fix**: Reduce `StateConstraint`, use symmetry reduction

**Problem**: "CHOOSE evaluation failed"
- **Cause**: Abstract functions not properly defined
- **Fix**: Ensure `ParseDocID` and `ComputeChecksum` are declared as CONSTANTS with ASSUME axioms

## Integration with CI

### GitHub Actions Example

```yaml
name: Formal Verification

on: [push, pull_request]

jobs:
  alloy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-java@v4
        with:
          java-version: '11'
      - name: Download Alloy
        run: wget https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.1.0/org.alloytools.alloy.dist.jar
      - name: Run Alloy checks
        run: java -jar org.alloytools.alloy.dist.jar --check formal/shirushi.als

  tla:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-java@v4
        with:
          java-version: '11'
      - name: Download TLA+ Tools
        run: wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
      - name: Run TLC
        run: java -jar tla2tools.jar -workers auto -config formal/shirushi.cfg formal/shirushi.tla
```

## Contributing

When modifying formal specifications:

1. **Document changes** in commit messages
2. **Verify all assertions** still pass
3. **Update VERIFICATION_STRATEGY.md** if verification approach changes
4. **Add new test cases** for new dimensions/operations

## References

- [Alloy Documentation](https://alloytools.org/documentation.html)
- [Alloy Tutorial](https://alloytools.org/tutorials/online/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [TLA+ Hyperbook](https://learntla.com/)
- [Lightweight Formal Methods in Practice](https://www.hillelwayne.com/post/fms-for-the-working-dev/)
- [TLC Model Checker Guide](https://lamport.azurewebsites.net/tla/tlc.html)

## License

Same as parent project (MIT License).
