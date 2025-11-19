#!/bin/bash
# Shirushi Formal Verification Runner
# Runs both Alloy and TLA+ (Apalache) verification

set -e  # Exit on error
set -o pipefail  # Catch errors in pipes

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTPUT_DIR="${SCRIPT_DIR}/output"
ALLOY_FILE="${SCRIPT_DIR}/shirushi.als"
TLA_FILE="${SCRIPT_DIR}/shirushi.tla"
APALACHE_CFG="${SCRIPT_DIR}/apalache.cfg"

# Tool paths (can be overridden by environment)
APALACHE_CMD="${APALACHE_CMD:-apalache-mc}"
ALLOY_CLI_JAR="${ALLOY_CLI_JAR:-$HOME/.alloy-cli/AlloyCommandline.jar}"

# Create output directory
mkdir -p "${OUTPUT_DIR}"

# Track failures
FAILURES=0

echo "========================================="
echo "Shirushi Formal Verification"
echo "========================================="
echo ""

# Function to print status
print_status() {
    if [ $1 -eq 0 ]; then
        echo -e "${GREEN}✓${NC} $2"
    else
        echo -e "${RED}✗${NC} $2"
        FAILURES=$((FAILURES + 1))
    fi
}

# =========================================
# Part 1: TLA+ Type Checking
# =========================================
echo -e "${YELLOW}[1/4]${NC} TLA+ Type Checking with Apalache..."
if command -v "${APALACHE_CMD}" >/dev/null 2>&1; then
    if "${APALACHE_CMD}" typecheck "${TLA_FILE}" 2>&1 | tee "${OUTPUT_DIR}/apalache-typecheck.log"; then
        print_status 0 "TLA+ type checking passed"
    else
        print_status 1 "TLA+ type checking failed"
    fi
else
    echo -e "${RED}WARNING:${NC} Apalache not found. Skipping TLA+ verification."
    echo "Install from: https://github.com/informalsystems/apalache/releases"
fi
echo ""

# =========================================
# Part 2: TLA+ Model Checking
# =========================================
echo -e "${YELLOW}[2/4]${NC} TLA+ Model Checking with Apalache..."
if command -v "${APALACHE_CMD}" >/dev/null 2>&1; then
    if "${APALACHE_CMD}" check \
        --config="${APALACHE_CFG}" \
        --write-json \
        --out-dir="${OUTPUT_DIR}/apalache" \
        "${TLA_FILE}" 2>&1 | tee "${OUTPUT_DIR}/apalache-check.log"; then
        print_status 0 "TLA+ model checking passed"
    else
        print_status 1 "TLA+ model checking failed"

        # Check for counterexample
        if [ -f "${OUTPUT_DIR}/apalache/counterexample.tla" ]; then
            echo -e "${YELLOW}Counterexample found:${NC}"
            head -n 20 "${OUTPUT_DIR}/apalache/counterexample.tla"
            echo "... (see full file at ${OUTPUT_DIR}/apalache/counterexample.tla)"
        fi
    fi
else
    echo -e "${YELLOW}SKIPPED:${NC} Apalache not installed"
fi
echo ""

# =========================================
# Part 3: Alloy Checking
# =========================================
echo -e "${YELLOW}[3/4]${NC} Alloy Specification Checking..."
if [ -f "${ALLOY_CLI_JAR}" ]; then
    if java -jar "${ALLOY_CLI_JAR}" "${ALLOY_FILE}" 2>&1 | tee "${OUTPUT_DIR}/alloy-check.log"; then
        print_status 0 "Alloy checking passed"
    else
        print_status 1 "Alloy checking failed"
    fi
elif command -v java >/dev/null 2>&1; then
    echo -e "${RED}WARNING:${NC} AlloyCommandline.jar not found at ${ALLOY_CLI_JAR}"
    echo "Download from: https://github.com/draftcode/AlloyCommandline"
    echo -e "${YELLOW}SKIPPED:${NC} Alloy verification"
else
    echo -e "${RED}ERROR:${NC} Java not found. Cannot run Alloy."
    FAILURES=$((FAILURES + 1))
fi
echo ""

# =========================================
# Part 4: Summary
# =========================================
echo "========================================="
echo "Verification Summary"
echo "========================================="

if [ $FAILURES -eq 0 ]; then
    echo -e "${GREEN}✓ All formal verifications passed!${NC}"
    echo ""
    echo "Output files saved to: ${OUTPUT_DIR}"
    exit 0
else
    echo -e "${RED}✗ ${FAILURES} verification(s) failed${NC}"
    echo ""
    echo "Check logs in: ${OUTPUT_DIR}"
    echo ""
    echo "Common issues:"
    echo "  - Apalache not installed: brew install apalache"
    echo "  - AlloyCommandline not found: download from GitHub"
    echo "  - Java not found: install OpenJDK 17+"
    exit 1
fi
