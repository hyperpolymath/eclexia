# SPDX-License-Identifier: PMPL-1.0-or-later
# Multi-stage Containerfile for Eclexia (Podman + Chainguard)
# Target: <50MB image, <5min build time

# Stage 1: Build environment (Wolfi-based, has apk + musl toolchain)
FROM cgr.dev/chainguard/rust:latest-dev AS builder

RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    ca-certificates

WORKDIR /build

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

RUN mkdir -p \
    compiler/eclexia-ast/src compiler/eclexia-lexer/src compiler/eclexia-parser/src \
    compiler/eclexia-typeck/src compiler/eclexia-hir/src compiler/eclexia-mir/src \
    compiler/eclexia-codegen/src compiler/eclexia-interp/src compiler/eclexia-fmt/src \
    compiler/eclexia-lint/src compiler/eclexia-debugger/src compiler/eclexia-doc/src \
    compiler/eclexia/src runtime/eclexia-runtime/src && \
    echo "fn main() {}" > compiler/eclexia/src/main.rs && \
    touch compiler/eclexia-ast/src/lib.rs compiler/eclexia-lexer/src/lib.rs \
          compiler/eclexia-parser/src/lib.rs compiler/eclexia-typeck/src/lib.rs \
          compiler/eclexia-hir/src/lib.rs compiler/eclexia-mir/src/lib.rs \
          compiler/eclexia-codegen/src/lib.rs compiler/eclexia-interp/src/lib.rs \
          compiler/eclexia-fmt/src/lib.rs compiler/eclexia-lint/src/lib.rs \
          compiler/eclexia-debugger/src/lib.rs compiler/eclexia-doc/src/lib.rs \
          runtime/eclexia-runtime/src/lib.rs

RUN cargo build --release --bin eclexia
RUN rm -rf compiler/*/src runtime/*/src

COPY compiler/ compiler/
COPY runtime/ runtime/
COPY stdlib/ stdlib/

RUN cargo build --release --bin eclexia && strip target/release/eclexia

# Stage 2: Minimal Chainguard static runtime (distroless, nonroot uid 65532 by default)
FROM cgr.dev/chainguard/static:latest

COPY --from=builder /build/target/release/eclexia /usr/local/bin/eclexia
COPY --from=builder /build/stdlib /usr/local/lib/eclexia/stdlib

ENV ECLEXIA_STDLIB_PATH=/usr/local/lib/eclexia/stdlib

ENTRYPOINT ["/usr/local/bin/eclexia"]
CMD ["--help"]

LABEL org.opencontainers.image.title="Eclexia" \
      org.opencontainers.image.description="Resource-aware programming language" \
      org.opencontainers.image.version="0.1.0" \
      org.opencontainers.image.authors="Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>" \
      org.opencontainers.image.source="https://github.com/hyperpolymath/eclexia" \
      org.opencontainers.image.licenses="PMPL-1.0-or-later"
