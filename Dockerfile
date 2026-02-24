# SPDX-License-Identifier: PMPL-1.0-or-later
# Multi-stage Dockerfile for Eclexia
# Target: <50MB image, <5min build time

# Stage 1: Build environment
FROM rust:1.75-alpine AS builder

# Install build dependencies
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    ca-certificates

# Set working directory
WORKDIR /build

# Copy dependency manifests first (for layer caching)
COPY Cargo.toml Cargo.lock ./
COPY compiler/eclexia-ast/Cargo.toml compiler/eclexia-ast/
COPY compiler/eclexia-lexer/Cargo.toml compiler/eclexia-lexer/
COPY compiler/eclexia-parser/Cargo.toml compiler/eclexia-parser/
COPY compiler/eclexia-typeck/Cargo.toml compiler/eclexia-typeck/
COPY compiler/eclexia-hir/Cargo.toml compiler/eclexia-hir/
COPY compiler/eclexia-mir/Cargo.toml compiler/eclexia-mir/
COPY compiler/eclexia-codegen/Cargo.toml compiler/eclexia-codegen/
COPY compiler/eclexia-interp/Cargo.toml compiler/eclexia-interp/
COPY compiler/eclexia-fmt/Cargo.toml compiler/eclexia-fmt/
COPY compiler/eclexia-lint/Cargo.toml compiler/eclexia-lint/
COPY compiler/eclexia-debugger/Cargo.toml compiler/eclexia-debugger/
COPY compiler/eclexia-doc/Cargo.toml compiler/eclexia-doc/
COPY compiler/eclexia/Cargo.toml compiler/eclexia/
COPY runtime/eclexia-runtime/Cargo.toml runtime/eclexia-runtime/

# Create dummy source files to cache dependencies
RUN mkdir -p \
    compiler/eclexia-ast/src \
    compiler/eclexia-lexer/src \
    compiler/eclexia-parser/src \
    compiler/eclexia-typeck/src \
    compiler/eclexia-hir/src \
    compiler/eclexia-mir/src \
    compiler/eclexia-codegen/src \
    compiler/eclexia-interp/src \
    compiler/eclexia-fmt/src \
    compiler/eclexia-lint/src \
    compiler/eclexia-debugger/src \
    compiler/eclexia-doc/src \
    compiler/eclexia/src \
    runtime/eclexia-runtime/src && \
    echo "fn main() {}" > compiler/eclexia/src/main.rs && \
    touch compiler/eclexia-ast/src/lib.rs \
          compiler/eclexia-lexer/src/lib.rs \
          compiler/eclexia-parser/src/lib.rs \
          compiler/eclexia-typeck/src/lib.rs \
          compiler/eclexia-hir/src/lib.rs \
          compiler/eclexia-mir/src/lib.rs \
          compiler/eclexia-codegen/src/lib.rs \
          compiler/eclexia-interp/src/lib.rs \
          compiler/eclexia-fmt/src/lib.rs \
          compiler/eclexia-lint/src/lib.rs \
          compiler/eclexia-debugger/src/lib.rs \
          compiler/eclexia-doc/src/lib.rs \
          runtime/eclexia-runtime/src/lib.rs

# Build dependencies (cached layer)
RUN cargo build --release --bin eclexia

# Remove dummy sources
RUN rm -rf compiler/*/src runtime/*/src

# Copy actual source code
COPY compiler/ compiler/
COPY runtime/ runtime/
COPY stdlib/ stdlib/

# Build actual binary
RUN cargo build --release --bin eclexia && \
    strip target/release/eclexia

# Stage 2: Runtime environment
FROM alpine:3.19

# Install runtime dependencies only
RUN apk add --no-cache \
    ca-certificates \
    libgcc

# Create non-root user
RUN addgroup -g 1000 eclexia && \
    adduser -D -u 1000 -G eclexia eclexia

# Copy binary from builder
COPY --from=builder /build/target/release/eclexia /usr/local/bin/eclexia

# Copy stdlib
COPY --from=builder /build/stdlib /usr/local/lib/eclexia/stdlib

# Set up environment
ENV ECLEXIA_STDLIB_PATH=/usr/local/lib/eclexia/stdlib
ENV PATH="/usr/local/bin:${PATH}"

# Switch to non-root user
USER eclexia
WORKDIR /home/eclexia

# Verify installation
RUN eclexia --version

# Default command
CMD ["eclexia", "--help"]

# Labels
LABEL org.opencontainers.image.title="Eclexia" \
      org.opencontainers.image.description="Resource-aware programming language" \
      org.opencontainers.image.version="0.1.0" \
      org.opencontainers.image.authors="Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>" \
      org.opencontainers.image.source="https://github.com/hyperpolymath/eclexia" \
      org.opencontainers.image.licenses="PMPL-1.0-or-later"
