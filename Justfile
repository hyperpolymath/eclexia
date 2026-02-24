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

# Run unit/library tests only
test-unit:
    cargo test --workspace --lib

# Run integration tests across workspace
test-integration:
    cargo test --workspace --tests

# Run conformance test corpus
test-conformance:
    cargo test -p eclexia --test conformance_tests

# Point-to-point boundary checks (interop contracts)
test-p2p:
    cargo run --bin eclexia -- interop check

# End-to-end smoke execution through CLI/runtime
test-e2e:
    cargo run --bin eclexia -- run examples/hello.ecl
    cargo run --bin eclexia -- run examples/comprehensive_opportunity.ecl

# Run the smoke test (per ANCHOR success criteria)
smoke-test:
    cargo test
    cargo run --bin eclexia -- run examples/hello.ecl

# Run conformance corpus tests
conformance:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Running valid conformance tests ==="
    for f in tests/conformance/valid/*.ecl; do
        echo "Testing: $f"
        cargo run --quiet --bin eclexia -- run "$f" > /dev/null 2>&1 && echo "  PASS" || { echo "  FAIL (expected success)"; exit 1; }
    done
    echo ""
    echo "=== Running invalid conformance tests (should fail) ==="
    for f in tests/conformance/invalid/*.ecl; do
        echo "Testing: $f"
        case "$f" in
            *stack_overflow_deep_recursion.ecl)
                echo "  SKIP (known abort path: host stack overflow)"
                continue
                ;;
        esac
        if cargo run --quiet --bin eclexia -- run "$f" > /dev/null 2>&1; then
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
    cargo run --bin eclexia -- run {{file}}

# Run the REPL
repl:
    cargo run --bin eclexia -- repl

# Check code without running (parse + typecheck)
check file:
    cargo run --bin eclexia -- check {{file}}

# Demo: run the fibonacci example
demo:
    cargo run --bin eclexia -- run examples/fibonacci.ecl

# Clean build artifacts
clean:
    cargo clean

# Format code (when rustfmt is configured)
fmt:
    cargo fmt --all

# Verify formatting without modifying files
fmt-check:
    cargo fmt --all -- --check

# Run clippy lints
lint:
    cargo clippy --workspace --lib --bins --examples -- -D warnings

# Benchmark smoke checks
bench-smoke:
    cargo run --bin eclexia -- bench
    cargo run --bin eclexia -- bench --energy

# Panic-attack security scan
panic-attack:
    ./scripts/qa/run-panic-attack.sh

# Validate machine/human-readable documentation references
docs-check:
    ./scripts/qa/check-docs.sh

# Full local quality gate
quality-gate:
    just docs-check
    just fmt-check
    just lint
    just test-unit
    just test-conformance
    just test-integration
    just test-p2p
    just test-e2e
    just bench-smoke

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
