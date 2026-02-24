# Eclexia for Users

## Prerequisites

- Rust toolchain (1.75+)
- Cargo

## Quick Start

```bash
cargo build --release
cargo run -- run examples/hello.ecl
```

## Typical Workflow

```bash
# Type-check a program
cargo run -- check path/to/file.ecl

# Run a program
cargo run -- run path/to/file.ecl

# Run tests
cargo test --workspace
```

## Where to Learn

- [`../../GETTING_STARTED.md`](../../GETTING_STARTED.md)
- [`../../SPECIFICATION.md`](../../SPECIFICATION.md)
- [`../../examples/`](../../examples/)

## Current Caveats

- Some advanced features remain in-progress
- Some backend/runtime paths are still being hardened
- Benchmarks exist but should be treated as evolving evidence

See [`../../QUICK_STATUS.md`](../../QUICK_STATUS.md) for current limits.
