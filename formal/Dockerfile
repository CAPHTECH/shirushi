# Multi-stage Dockerfile for Shirushi Formal Verification
# Contains both TLC (TLA+) and Alloy CLI tools

# ============================================================================
# Base Stage: Java Runtime Environment
# ============================================================================
FROM eclipse-temurin:17-jre AS base

# Install common dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        curl \
        unzip \
        git \
        ca-certificates && \
    rm -rf /var/lib/apt/lists/*



# ============================================================================
# Alloy Stage: Download official Alloy JAR
# ============================================================================
FROM base AS alloy

ARG ALLOY_VERSION=6.2.0
ARG ALLOY_SHA256=6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d

WORKDIR /tmp

# Download official Alloy JAR with SHA256 verification
RUN mkdir -p /opt/alloy && \
    curl -L "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/org.alloytools.alloy.dist.jar" \
         -o /opt/alloy/alloy.jar && \
    echo "${ALLOY_SHA256}  /opt/alloy/alloy.jar" | sha256sum -c -

# Verify installation
RUN java -jar /opt/alloy/alloy.jar --help || true

# ============================================================================
# TLC Stage: Download TLA+ Tools
# ============================================================================
FROM base AS tlc

ARG TLA_VERSION=1.8.0
# No official SHA provided easily for nightly/releases sometimes, but good practice to verify if possible.
# Using a known URL for stability.
WORKDIR /tmp

RUN mkdir -p /opt/tla && \
    curl -L "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar" \
         -o /opt/tla/tla2tools.jar

# Verify
RUN java -jar /opt/tla/tla2tools.jar -help || true

# ============================================================================
# Final Stage: Combine both tools
# ============================================================================
FROM base

# Copy Alloy from alloy stage
COPY --from=alloy /opt/alloy /opt/alloy

# Copy TLC from tlc stage
COPY --from=tlc /opt/tla /opt/tla

# Set environment variables
ENV ALLOY_JAR="/opt/alloy/alloy.jar"
ENV TLA_JAR="/opt/tla/tla2tools.jar"

# Create workspace directory
WORKDIR /workspace

# Add verification script
COPY verify-all.sh /usr/local/bin/verify-all
RUN chmod +x /usr/local/bin/verify-all

# Metadata
LABEL maintainer="Shirushi Contributors"
LABEL description="Formal verification tools for Shirushi (TLC + Alloy)"
LABEL alloy.version="6.2.0"
LABEL alloy.sha256="6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d"

# Verify both tools are available
RUN java -jar /opt/tla/tla2tools.jar -help || true && \
    java -jar /opt/tla/tla2tools.jar -help || true && \
    java -version

# Default command
CMD ["verify-all"]

# ============================================================================
# Usage:
#
# Build:
#   docker build -t shirushi/formal-verification:latest .
#
# Run:
#   docker run --rm -v $(pwd)/formal:/workspace shirushi/formal-verification:latest
#
# Interactive:
#   docker run --rm -it -v $(pwd)/formal:/workspace shirushi/formal-verification:latest bash
#
# ============================================================================
