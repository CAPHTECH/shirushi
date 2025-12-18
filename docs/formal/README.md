---
doc_id: SHI-FORMAL-2025-0001-F
title: Shirushi Formal Specifications
version: "0.1.0"
status: Draft
created_at: 2025-11-19
---

# Shirushi Formal Specifications

This directory contains formal verification artifacts for the Shirushi document ID management system using **Alloy** and **TLA+**.

## Contents

**Specifications:**
- **`shirushi.als`** - Alloy structural specification (invariants and constraints)
- **`shirushi.tla`** - TLA+ temporal specification (state transitions and properties)
- **`shirushi.cfg`** - TLC model checker configuration (deprecated, use apalache.cfg)
- **`apalache.cfg`** - Apalache configuration for TLA+ model checking

**Infrastructure:**
- **`Dockerfile`** - Multi-stage Docker image with Apalache + Alloy CLI
- **`docker-compose.yml`** - Docker Compose configuration for local testing
- **`verify-all.sh`** - Unified verification script (runs both tools)
- **`.github/workflows/formal-verification.yml`** - GitHub Actions CI workflow

**Documentation:**
- **`VERIFICATION_STRATEGY.md`** - Comprehensive verification approach documentation
- **`CI_INTEGRATION_DESIGN.md`** - CI/CD integration design and architecture
- **`FORMAL_SYNC_SPEC.md`** - Config→formal constant generation CLI specification
- **`DESIGN_DIALOGUE.md`** - Two-role architecture discussion log (decision trace)
- **`README.md`** - This file

## Quick Start

### Option 1: Using Docker (Recommended for CI)

The easiest way to run formal verification is using Docker:

```bash
# Run all verifications
docker-compose run --rm verify

# Run only TLA+ checks
docker-compose run --rm apalache

# Run only Alloy checks
docker-compose run --rm alloy

# Interactive shell
docker-compose run --rm shell
```

**First time setup:**
```bash
cd formal
docker-compose build
```

### Option 2: Using Local Script

```bash
cd formal
./verify-all.sh
```

This script will:
1. Check if Apalache is installed, run TLA+ verification
2. Check if AlloyCommandline is installed, run Alloy verification
3. Generate reports in `output/` directory

### Option 3: Manual Installation

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

## Continuous Integration

### GitHub Actions

Formal verification runs automatically on every push and pull request. See `.github/workflows/formal-verification.yml` for the full workflow.

**Status badges:**
![Formal Verification](https://github.com/YOUR_ORG/shirushi/actions/workflows/formal-verification.yml/badge.svg)

**What's verified:**
- ✅ Alloy structural invariants
- ✅ TLA+ type checking
- ✅ TLA+ model checking with Apalache
- ✅ Counterexample generation on failures

**Artifacts:**
- Verification logs
- Counterexamples (if found)
- JSON reports

**Manual trigger:**
```bash
# Via GitHub UI: Actions tab → Formal Verification → Run workflow

# Via GitHub CLI
gh workflow run formal-verification.yml
```

### Docker-based CI

The provided `Dockerfile` can be used in any CI system:

**GitHub Actions:**
```yaml
- name: Run verification
  run: |
    docker build -t shirushi-verify formal/
    docker run --rm -v $PWD/formal:/workspace shirushi-verify
```

**GitLab CI:**
```yaml
verify:
  image: docker:latest
  services:
    - docker:dind
  script:
    - docker build -t shirushi-verify formal/
    - docker run --rm -v $PWD/formal:/workspace shirushi-verify
```

**Jenkins:**
```groovy
stage('Formal Verification') {
  steps {
    sh 'docker build -t shirushi-verify formal/'
    sh 'docker run --rm -v $PWD/formal:/workspace shirushi-verify'
  }
}
```

### Local Pre-commit Hook

Add to `.git/hooks/pre-commit`:
```bash
#!/bin/bash
if git diff --cached --name-only | grep -q "^formal/"; then
  echo "Running formal verification..."
  cd formal && ./verify-all.sh
  if [ $? -ne 0 ]; then
    echo "❌ Formal verification failed. Commit aborted."
    exit 1
  fi
fi
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
