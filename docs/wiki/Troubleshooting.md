# Troubleshooting

## Build Fails

- Confirm Rust/Cargo versions
- Run `cargo clean` then rebuild
- Re-run with `cargo build -vv` for verbose diagnostics

## Tests Failing

- Start with `cargo test --workspace --lib`
- Then run integration and conformance separately
- Check whether failures are parser/runtime/interop specific

## LLVM/WASM Backend Issues

- Verify toolchain dependencies are present
- Compare behavior against VM/interpreter path
- Use status docs to confirm current backend maturity

## Interop or FFI Issues

- Run `cargo run -- interop check`
- Verify Zig FFI and Idris ABI contracts are in sync

## Security Scan Fails

- Run `just panic-attack`
- Address critical/high findings first
- Re-run until clean
