# Eclexia Nextgen-Languages Interop Status

Last updated: 2026-02-09

## Architecture

All interop uses the **bidirectional ABI/FFI** pattern:
- **Outbound** (Eclexia → native): Idris2 ABI definitions + Zig FFI implementation
- **Inbound** (external → Eclexia runtime): C-compatible headers (`generated/abi/eclexia_ffi.h`)

## Language Status

### Tier 1: Ready (have FFI infrastructure)

| Language | Build System | FFI Mechanism | Status |
|----------|-------------|---------------|--------|
| WokeLang | Cargo (Rust) | Has `src/ffi/c_api.rs`, Zig bridge | Bridge config created |
| Phronesis | Mix (Elixir) | Elixir NIFs | Bridge config created |
| betlang | Racket | `ffi/unsafe` | Bridge config created |

### Tier 2: Needs minor work

| Language | Build System | FFI Mechanism | Status |
|----------|-------------|---------------|--------|
| AffineScript | Dune (OCaml) | `ctypes` | Pending OCaml binding |
| 7-tentacles | ReScript | Deno `dlopen` | Educational — low priority |

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
