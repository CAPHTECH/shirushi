# Multi-stage Dockerfile for Shirushi Formal Verification
# Contains both Apalache (TLA+) and Alloy CLI tools

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
# Apalache Stage: Download and install Apalache
# ============================================================================
FROM base AS apalache

ARG APALACHE_VERSION=0.45.7

WORKDIR /tmp

# Download and install Apalache
RUN curl -LO "https://github.com/informalsystems/apalache/releases/download/v${APALACHE_VERSION}/apalache-${APALACHE_VERSION}.zip" && \
    unzip -q "apalache-${APALACHE_VERSION}.zip" && \
    mv "apalache-${APALACHE_VERSION}" /opt/apalache && \
    rm "apalache-${APALACHE_VERSION}.zip"

# Verify installation
RUN /opt/apalache/bin/apalache-mc version

# ============================================================================
# Alloy Stage: Download Alloy and build AlloyCommandline
# ============================================================================
FROM base AS alloy

ARG ALLOY_VERSION=6.1.0

# Install build dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        gradle && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /tmp

# Download official Alloy jar
RUN mkdir -p /opt/alloy && \
    curl -L "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/org.alloytools.alloy.dist.jar" \
         -o /opt/alloy/alloy.jar

# Build AlloyCommandline from source
RUN git clone --depth 1 https://github.com/draftcode/AlloyCommandline.git /tmp/alloy-cli && \
    cd /tmp/alloy-cli && \
    gradle build && \
    cp build/libs/AlloyCommandline.jar /opt/alloy/alloy-cli.jar

# Verify installation
RUN java -jar /opt/alloy/alloy.jar --help || true

# ============================================================================
# Final Stage: Combine both tools
# ============================================================================
FROM base

# Copy Apalache from apalache stage
COPY --from=apalache /opt/apalache /opt/apalache

# Copy Alloy from alloy stage
COPY --from=alloy /opt/alloy /opt/alloy

# Set environment variables
ENV PATH="/opt/apalache/bin:${PATH}"
ENV ALLOY_JAR="/opt/alloy/alloy.jar"
ENV ALLOY_CLI_JAR="/opt/alloy/alloy-cli.jar"
ENV APALACHE_HOME="/opt/apalache"

# Create workspace directory
WORKDIR /workspace

# Add verification script
COPY verify-all.sh /usr/local/bin/verify-all
RUN chmod +x /usr/local/bin/verify-all

# Metadata
LABEL maintainer="Shirushi Contributors"
LABEL description="Formal verification tools for Shirushi (Apalache + Alloy)"
LABEL apalache.version="0.45.7"
LABEL alloy.version="6.1.0"

# Verify both tools are available
RUN apalache-mc version && \
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
