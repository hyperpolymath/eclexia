# Eclexia ABI/FFI Boundary (RC4)

## Purpose

Eclexia uses a two-lane boundary model:

- **Stable lane**: existing C ABI + Zig FFI symbols stay compatible.
- **Extension lane**: additive APIs are introduced for new capabilities.

This allows ABI growth without breaking current consumers.

## Reinforcement Policy

`proven` is used as **targeted reinforcement** for critical paths, not as a language takeover strategy.

- Keep Rust (and other practical languages) for most implementation work.
- Use Idris2-backed/proven components where failure cost is high.
- Typical candidates: safe crypto, path/URL/JSON/network validation, critical ABI invariants.
- Avoid forcing high-assurance tooling where it would materially damage delivery, operability, or adoption.

## Architecture

```text
Eclexia language/runtime
  -> Idris2 ABI model (src/abi/ResourceABI.idr)
    -> C ABI header (generated/abi/eclexia_ffi.h)
      -> Zig FFI implementation (ffi/zig/src/resource.zig)
        -> consumers (Rust/C/Python/etc.)
```

## ABI Compatibility Contract

- Existing symbols remain available.
- Additions are introduced via new symbols and option structs.
- New structs are forward-compatible via `struct_size` fields.
- Runtime capability negotiation is available through `ecl_abi_get_info`.

## RC4 Additions

- `ecl_abi_get_info(ecl_abi_info_t *out_info)`
  - Returns ABI version + feature bitset.
- `ecl_tracker_create_ex(uint32_t dimension, double total_budget, const ecl_tracker_options_t *options)`
  - Extended tracker creation with forward-compatible options.
- `ecl_tracker_snapshot(uint64_t tracker_handle, ecl_budget_t *out_budget, uint64_t *timestamp_ns_out)`
  - Stable snapshot of tracker state with optional timestamp.
- `ecl_sla_check` now uses typed `ecl_sla_constraint_t` instead of `void *`.

## Selected Feature Flags

- `ECL_ABI_FEATURE_BATCH`
- `ECL_ABI_FEATURE_LOCK_FREE`
- `ECL_ABI_FEATURE_BIDIRECTIONAL`
- `ECL_ABI_FEATURE_EXTENDED_TRACKER`
- `ECL_ABI_FEATURE_ABI_INTROSPECTION`

## Build and Test

```bash
cd ffi/zig
zig build
zig build test
```

From repo root:

```bash
just docs-check
just quality-gate
```

## Proven Cross-Repo Guardrails

Documentation and CI expect the sibling `proven` repository for high-assurance bindings referenced by examples.

- Local default path: `../proven`
- Override path: `PROVEN_ROOT=/path/to/proven`
- CI enforcement: `ECLEXIA_REQUIRE_PROVEN=1`

