# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
#
# Eclexia justfile - local task runner
# All local operations must be invoked via `just <recipe>`

# Default recipe: show available recipes
default:
    @just --list

# Build the compiler
build:
    cargo build

# Build release version
build-release:
    cargo build --release

# Run all tests
test:
    cargo test

# Run the smoke test (per ANCHOR success criteria)
smoke-test:
    cargo test
    cargo run -- run examples/hello.ecl

# Run conformance corpus tests
conformance:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Running valid conformance tests ==="
    for f in tests/conformance/valid/*.ecl; do
        echo "Testing: $f"
        cargo run --quiet -- run "$f" > /dev/null 2>&1 && echo "  PASS" || { echo "  FAIL (expected success)"; exit 1; }
    done
    echo ""
    echo "=== Running invalid conformance tests (should fail) ==="
    for f in tests/conformance/invalid/*.ecl; do
        echo "Testing: $f"
        if cargo run --quiet -- run "$f" > /dev/null 2>&1; then
            echo "  FAIL (expected ResourceViolation)"
            exit 1
        else
            echo "  PASS (correctly rejected)"
        fi
    done
    echo ""
    echo "All conformance tests passed!"

# Run a specific .ecl file
run file:
    cargo run -- run {{file}}

# Run the REPL
repl:
    cargo run -- repl

# Check code without running (parse + typecheck)
check file:
    cargo run -- check {{file}}

# Demo: run the fibonacci example
demo:
    cargo run -- run examples/fibonacci.ecl

# Clean build artifacts
clean:
    cargo clean

# Format code (when rustfmt is configured)
fmt:
    cargo fmt --all

# Run clippy lints
lint:
    cargo clippy --all-targets --all-features

# Show project status
status:
    @echo "=== Git Status ==="
    @git status --short
    @echo ""
    @echo "=== Build Status ==="
    @cargo build 2>&1 | tail -3
    @echo ""
    @echo "=== Test Status ==="
    @cargo test 2>&1 | grep -E "^(test result|running)" | tail -2
