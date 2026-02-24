# Eclexia Nextgen-Languages Interop Status

Last updated: 2026-02-12

## Architecture

All interop uses the **bidirectional ABI/FFI** pattern:
- **Outbound** (Eclexia -> native): Idris2 ABI definitions + Zig FFI implementation
- **Inbound** (external -> Eclexia runtime): C-compatible headers (`generated/abi/eclexia_ffi.h`)

## CLI Integration

The `eclexia interop check` command validates all bridge configurations:
- Checks bridge TOML files in `interop/`
- Verifies referenced FFI entry points exist
- Reports bridge status (connected, available, stub)
- Run: `cargo run -- interop check`

## Language Status

### Tier 1: Ready (have FFI infrastructure)

| Language | Build System | FFI Mechanism | Status |
|----------|-------------|---------------|--------|
| WokeLang | Cargo (Rust) | Has `src/ffi/c_api.rs`, Zig bridge | Bridge config created, validator checks pass |
| Phronesis | Mix (Elixir) | Elixir NIFs | Bridge config created, validator checks pass |
| betlang | Racket | `ffi/unsafe` | Bridge config created, validator checks pass |

### Tier 2: Needs minor work

| Language | Build System | FFI Mechanism | Status |
|----------|-------------|---------------|--------|
| AffineScript | Dune (OCaml) | `ctypes` | Bridge config created, pending OCaml binding |
| 7-tentacles | ReScript | Deno `dlopen` | Educational -- low priority |

### Tier 3: Blocked on language implementation

| Language | Status | Notes |
|----------|--------|-------|
| Julia-the-Viper | Stub | Only README exists |
| My-Lang | Stub | Only README exists |
| Ephapax | Stub | RSR structure only |
| Anvomidav | Stub | RSR structure only |
| Oblibeny | Stub | Recently added, no source |
| Error-Lang | Unknown | Needs investigation |

### Query Languages (VQL/GQL)

| Language | Variant | Status |
|----------|---------|--------|
| VQL | Standard | Integrated via VeriSimDB |
| VQL-DT | Dependent Types | Needs eclexia type bridge |
| GQL-DT | Dependent Types | Needs eclexia type bridge |
| FBQL-DT | Dependent Types | Needs eclexia type bridge |

## Bridge Configuration Files

Each `*_bridge.toml` describes:
- Language name and location
- FFI mechanism and entry points
- Eclexia runtime features to expose
- Build instructions

Bridge files:
- `wokelang_bridge.toml`
- `phronesis_bridge.toml`
- `betlang_bridge.toml`
- `affinescript_bridge.toml`

## FFI Directory

- `ffi/zig/src/eclexia_ffi.zig` - C-compatible wrappers for Eclexia runtime
- `ffi/zig/build.zig` - Build configuration
- `generated/abi/eclexia_ffi.h` - Generated C headers

## Native Runtime Library

The `eclexia-rt-native` crate provides a C-compatible static library with 5 symbols:
- `eclexia_rt_start()` - Initialize runtime
- `eclexia_rt_stop()` - Finalize and report
- `eclexia_rt_track_resource()` - Record resource usage
- `eclexia_rt_query_shadow_price()` - Query shadow prices
- `eclexia_rt_println()` - Print output

This library is used by the LLVM backend for linking native executables.
