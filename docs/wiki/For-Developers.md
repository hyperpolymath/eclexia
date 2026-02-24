# Eclexia for Developers

## Repository Layout

- `compiler/`: compiler crates and CLI front-end
- `runtime/`: runtime subsystems
- `libraries/`: ecosystem libraries
- `stdlib/`: standard library source
- `tests/`: conformance and integration tests
- `formal/`: Coq/Agda proof artifacts

## Core Engineering Commands

```bash
# Build
cargo build --workspace

# Test
cargo test --workspace

# Lint
cargo clippy --workspace --all-targets --all-features

# Format
cargo fmt --all
```

## Key Technical References

- [`../../SPECIFICATION.md`](../../SPECIFICATION.md)
- [`../../TOOLCHAIN_STATUS.md`](../../TOOLCHAIN_STATUS.md)
- [`../../IMPLEMENTATION_ROADMAP.md`](../../IMPLEMENTATION_ROADMAP.md)
- [`../../PROOFS.md`](../../PROOFS.md)
- [`../../FORMAL_VERIFICATION.md`](../../FORMAL_VERIFICATION.md)

## Contribution Entry Points

- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md)
- [`../../CODE_OF_CONDUCT.md`](../../CODE_OF_CONDUCT.md)
- [`../../SECURITY.md`](../../SECURITY.md)
