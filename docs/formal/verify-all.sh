#!/bin/bash
# Shirushi Formal Verification Runner
# Runs both Alloy and TLA+ (TLC) verification

set -e  # Exit on error
set -o pipefail  # Catch errors in pipes

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
SCRIPT_DIR="$(pwd)"
OUTPUT_DIR="${SCRIPT_DIR}/output"
ALLOY_FILE="${SCRIPT_DIR}/shirushi.als"
TLA_FILE="${SCRIPT_DIR}/shirushi.tla"

# Tool paths (can be overridden by environment)
ALLOY_JAR="${ALLOY_JAR:-$HOME/.alloy/org.alloytools.alloy.dist.jar}"

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
# Part 1: TLA+ Model Checking with TLC
# =========================================
echo -e "${YELLOW}[1/2]${NC} TLA+ Model Checking with TLC..."

# Check if TLA_JAR is set, otherwise try to find it
if [ -z "${TLA_JAR}" ]; then
    if [ -f "/opt/tla/tla2tools.jar" ]; then
        TLA_JAR="/opt/tla/tla2tools.jar"
    elif [ -f "tla2tools.jar" ]; then
        TLA_JAR="./tla2tools.jar"
    fi
fi

if [ -n "${TLA_JAR}" ] && [ -f "${TLA_JAR}" ]; then
    echo "Using TLC from: ${TLA_JAR}"
    
    # Run TLC
    if java -jar "${TLA_JAR}" -config shirushi.cfg shirushi.tla 2>&1 | tee "${OUTPUT_DIR}/tlc-check.log"; then
        # Check log for success message (TLC exit code isn't always 0 on success/failure in the way we want)
        if grep -q "Model checking completed. No error has been found." "${OUTPUT_DIR}/tlc-check.log"; then
            print_status 0 "TLA+ model checking passed"
        else
            print_status 1 "TLA+ model checking failed (see log)"
        fi
    else
        print_status 1 "TLA+ model checking failed to run"
    fi
else
    echo -e "${RED}WARNING:${NC} tla2tools.jar not found. Skipping TLA+ verification."
    echo "Set TLA_JAR environment variable or place tla2tools.jar in the current directory."
fi
echo ""
echo ""

# =========================================
# Part 3: Alloy Checking
# =========================================
echo -e "${YELLOW}[2/2]${NC} Alloy Specification Checking..."
if [ -f "${ALLOY_JAR}" ]; then
    # Run all commands (exec --command 0) and output to stdout (--output -)
    if java -jar "${ALLOY_JAR}" exec --command 0 --output - "${ALLOY_FILE}" 2>&1 | tee "${OUTPUT_DIR}/alloy-check.log"; then
        print_status 0 "Alloy checking passed"
    else
        print_status 1 "Alloy checking failed"
    fi
elif command -v java >/dev/null 2>&1; then
    echo -e "${RED}WARNING:${NC} Alloy JAR not found at ${ALLOY_JAR}"
    echo "Download from: https://github.com/AlloyTools/org.alloytools.alloy/releases"
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
    echo "  - TLC JAR not found: set TLA_JAR or place tla2tools.jar in current directory"
    echo "  - Alloy JAR not found: download from https://github.com/AlloyTools/org.alloytools.alloy/releases"
    echo "  - Java not found: install OpenJDK 17+"
    exit 1
fi
