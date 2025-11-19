# Formal Verification CI Integration Design

## Overview

This document outlines the design for integrating Apalache (TLA+) and Alloy CLI into the Shirushi CI/CD pipeline using GitHub Actions.

## Research Summary

### Apalache (TLA+ Model Checker)

**Tool Information:**
- GitHub: https://github.com/apalache-mc/apalache
- Docker Image: `ghcr.io/apalache-mc/apalache:main`
- Latest Release: 0.45.7+ (check releases page)
- Documentation: https://apalache-mc.org/

**Key Features:**
- Symbolic model checking using SMT solvers (Z3)
- CLI-friendly with `apalache-mc` command
- JSON output support for CI integration
- Counterexample generation
- Type checking with `typecheck` command

**CLI Usage:**
```bash
# Type check
apalache-mc typecheck spec.tla

# Model check with config
apalache-mc check --config=spec.cfg spec.tla

# Check specific invariant
apalache-mc check --inv=SystemInvariant spec.tla

# Generate JSON output
apalache-mc check --write-json --out-dir=output spec.tla
```

### Alloy CLI Tools

**Option 1: AlloyCommandline** (Recommended)
- GitHub: https://github.com/draftcode/AlloyCommandline
- Language: Java
- Runs all `run` and `check` commands in .als file
- Simple execution: `java -jar AlloyCommandline.jar spec.als`

**Option 2: kt-alloy-cli**
- GitHub: https://github.com/motemen/kt-alloy-cli
- Output: TAP (Test Anything Protocol) format
- Better for test result parsing

**Option 3: Official Alloy 6 CLI**
- `java -jar org.alloytools.alloy.dist.jar --run "Command" --file spec.als`
- More control over individual commands

## Architecture Design

### Docker Strategy

**Multi-stage Dockerfile** combining both tools:

```dockerfile
FROM eclipse-temurin:17-jre AS base

# Install Apalache
FROM base AS apalache
ARG APALACHE_VERSION=0.45.7
RUN apt-get update && apt-get install -y curl unzip && \
    curl -LO https://github.com/informalsystems/apalache/releases/download/v${APALACHE_VERSION}/apalache-${APALACHE_VERSION}.zip && \
    unzip -q apalache-${APALACHE_VERSION}.zip -d /opt/ && \
    mv /opt/apalache-${APALACHE_VERSION} /opt/apalache && \
    rm apalache-${APALACHE_VERSION}.zip

# Install Alloy CLI
FROM base AS alloy
ARG ALLOY_VERSION=6.1.0
RUN apt-get update && apt-get install -y curl && \
    mkdir -p /opt/alloy && \
    curl -L https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/org.alloytools.alloy.dist.jar \
         -o /opt/alloy/alloy.jar

# Install AlloyCommandline
RUN apt-get update && apt-get install -y git gradle && \
    git clone https://github.com/draftcode/AlloyCommandline.git /tmp/alloy-cli && \
    cd /tmp/alloy-cli && gradle build && \
    cp build/libs/AlloyCommandline.jar /opt/alloy/alloy-cli.jar && \
    rm -rf /tmp/alloy-cli

# Final image
FROM base
COPY --from=apalache /opt/apalache /opt/apalache
COPY --from=alloy /opt/alloy /opt/alloy

ENV PATH="/opt/apalache/bin:${PATH}"
ENV ALLOY_JAR="/opt/alloy/alloy.jar"
ENV ALLOY_CLI_JAR="/opt/alloy/alloy-cli.jar"

WORKDIR /workspace
```

**Benefits:**
- Single image contains both tools
- Reproducible environment
- Version pinning for stability
- Can be cached in GitHub Actions

### GitHub Actions Workflow Design

**Strategy:**
1. **Separate jobs** for Alloy and TLA+ (parallel execution)
2. **Caching** for Docker images and tool downloads
3. **Artifact upload** for counterexamples and error traces
4. **PR comments** for failure summaries

**Workflow Structure:**

```yaml
name: Formal Verification

on:
  push:
    branches: [main, develop]
    paths:
      - 'formal/**'
      - '.github/workflows/formal-verification.yml'
  pull_request:
    paths:
      - 'formal/**'

jobs:
  # Job 1: Alloy verification
  alloy:
    runs-on: ubuntu-latest
    timeout-minutes: 10

    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-java@v4
        with:
          distribution: 'temurin'
          java-version: '17'
          cache: 'gradle'

      - name: Cache Alloy CLI
        uses: actions/cache@v4
        with:
          path: ~/.alloy-cli
          key: alloy-cli-${{ runner.os }}-${{ hashFiles('formal/**/*.als') }}

      - name: Download AlloyCommandline
        run: |
          mkdir -p ~/.alloy-cli
          if [ ! -f ~/.alloy-cli/AlloyCommandline.jar ]; then
            # Build from source or download pre-built jar
            curl -L https://github.com/draftcode/AlloyCommandline/releases/.../AlloyCommandline.jar \
                 -o ~/.alloy-cli/AlloyCommandline.jar
          fi

      - name: Run Alloy Checks
        run: |
          java -jar ~/.alloy-cli/AlloyCommandline.jar formal/shirushi.als | tee alloy-output.txt

      - name: Upload Alloy Results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: alloy-results
          path: |
            alloy-output.txt
            *.xml

  # Job 2: TLA+ verification with Apalache
  tla:
    runs-on: ubuntu-latest
    timeout-minutes: 15

    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-java@v4
        with:
          distribution: 'temurin'
          java-version: '17'

      - name: Cache Apalache
        uses: actions/cache@v4
        with:
          path: ~/.apalache
          key: apalache-${{ runner.os }}-0.45.7

      - name: Install Apalache
        run: |
          if [ ! -d ~/.apalache/bin ]; then
            mkdir -p ~/.apalache
            curl -LO https://github.com/informalsystems/apalache/releases/download/v0.45.7/apalache-0.45.7.zip
            unzip -q apalache-0.45.7.zip -d ~/.apalache
            mv ~/.apalache/apalache-0.45.7/* ~/.apalache/
          fi
          echo "$HOME/.apalache/bin" >> $GITHUB_PATH

      - name: Type Check TLA+
        run: |
          apalache-mc typecheck formal/shirushi.tla

      - name: Model Check TLA+
        run: |
          apalache-mc check \
            --config=formal/shirushi.cfg \
            --write-json \
            --out-dir=output/apalache \
            formal/shirushi.tla

      - name: Upload Apalache Results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: apalache-results
          path: |
            output/apalache/**
            *.json

      - name: Comment PR with Results
        if: failure() && github.event_name == 'pull_request'
        uses: peter-evans/create-or-update-comment@v4
        with:
          issue-number: ${{ github.event.pull_request.number }}
          body: |
            ## ⚠️ Formal Verification Failed

            TLA+ model checking with Apalache found issues. Check the artifacts for counterexamples.

            [View run details](${{ github.server_url }}/${{ github.repository }}/actions/runs/${{ github.run_id }})

  # Job 3: Docker-based verification (optional, for future)
  docker-verify:
    runs-on: ubuntu-latest
    if: false  # Disabled by default, enable when Docker image is ready

    steps:
      - uses: actions/checkout@v4

      - name: Run verification in Docker
        run: |
          docker run --rm -v $PWD/formal:/workspace \
            ghcr.io/shirushi/formal-verification:latest \
            ./verify-all.sh
```

### Caching Strategy

**Tool Binaries:**
- Cache Apalache: `~/.apalache` with key `apalache-${{ runner.os }}-{version}`
- Cache Alloy CLI: `~/.alloy-cli` with key `alloy-cli-${{ runner.os }}-{hash}`
- Cache Docker layers: Use `docker/build-push-action` with `cache-from`/`cache-to`

**Java Dependencies:**
- Use `actions/setup-java` with `cache: gradle` or `cache: maven`

**Estimation:**
- Without cache: ~2-3 minutes to download and setup tools
- With cache: ~10-20 seconds

### Error Reporting Strategy

**Apalache Errors:**
1. Parse JSON output from `--write-json`
2. Extract counterexample from `counterexample.tla`
3. Extract trace from `trace.itf.json`
4. Format as GitHub PR comment with state transitions

**Alloy Errors:**
1. Parse stdout for assertion violations
2. Extract instance details
3. Format as PR comment or upload as artifact

**Example PR Comment Format:**
```markdown
## ⚠️ Formal Verification Failed

### TLA+ Model Checking (Apalache)
- ❌ Invariant `SystemInvariant` violated
- State trace: [View artifact](link)
- Counterexample found in 127 states

### Alloy Analysis
- ✅ All assertions passed
- ✅ No counterexamples found

**Details:**
See [workflow run](link) for full logs and artifacts.
```

## Implementation Phases

### Phase 1: Basic CI (Immediate)
- ✅ Setup GitHub Actions workflow
- ✅ Install tools from releases
- ✅ Run basic checks
- ✅ Upload artifacts on failure

### Phase 2: Docker Integration (Week 2)
- ✅ Create multi-stage Dockerfile
- ✅ Publish to GitHub Container Registry
- ✅ Update workflow to use Docker image
- ✅ Add caching for Docker layers

### Phase 3: Enhanced Reporting (Week 3)
- ✅ Parse Apalache JSON output
- ✅ Parse Alloy results
- ✅ Generate PR comments
- ✅ Create failure summaries

### Phase 4: Optimization (Week 4)
- ✅ Parallel matrix builds for multiple specs
- ✅ Incremental verification (only changed specs)
- ✅ Performance benchmarking
- ✅ Cache optimization

## Configuration Files Needed

### 1. Apalache Configuration (`formal/apalache.cfg`)
```
SPECIFICATION Spec
INVARIANTS
  TypeInvariant
  SystemInvariant
  ImmutabilityInvariant
PROPERTIES
  AlwaysValid
  LintReadOnly
```

### 2. Verification Script (`formal/verify-all.sh`)
```bash
#!/bin/bash
set -e

echo "=== Type Checking TLA+ ==="
apalache-mc typecheck shirushi.tla

echo "=== Model Checking TLA+ ==="
apalache-mc check --config=apalache.cfg --write-json --out-dir=output shirushi.tla

echo "=== Checking Alloy ==="
java -jar $ALLOY_CLI_JAR shirushi.als

echo "✅ All formal verifications passed"
```

### 3. Docker Compose (for local testing)
```yaml
version: '3.8'
services:
  verify:
    build: .
    volumes:
      - ./formal:/workspace
    command: ./verify-all.sh
```

## Cost Estimation

**GitHub Actions Minutes:**
- Alloy check: ~1-2 minutes
- TLA+ check: ~2-5 minutes
- Total per run: ~3-7 minutes
- Monthly estimate (assuming 100 runs): 300-700 minutes
- Cost: Free tier covers 2000 minutes/month

**Storage (Artifacts):**
- Per run: ~1-5 MB (counterexamples, traces)
- Monthly: ~100-500 MB
- Cost: Free tier covers 500 MB

## Success Metrics

1. **Reliability**: CI passes consistently for valid specs
2. **Speed**: Total verification time < 10 minutes
3. **Coverage**: All assertions and invariants checked
4. **Usability**: Clear error messages and counterexamples
5. **Maintenance**: Tool versions pinned and cached

## Next Steps

1. ✅ Review this design document
2. Create Dockerfile
3. Create GitHub Actions workflow
4. Create Apalache configuration
5. Create verification script
6. Test locally with Docker
7. Test in GitHub Actions
8. Document usage in README.md
9. Add badge to project README

## References

- [Apalache Documentation](https://apalache-mc.org/docs/apalache/)
- [AlloyCommandline GitHub](https://github.com/draftcode/AlloyCommandline)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Docker Best Practices](https://docs.docker.com/develop/dev-best-practices/)
