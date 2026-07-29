<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Architecture

Eclexia is a resource-typed language: energy, time, memory and carbon are
first-class in the type system, and execution is guided by shadow prices drawn
from linear-programming duality. This document describes where things live and
how data flows through the compiler.

## Compilation pipeline

Source (`.ecl`) enters at the lexer and leaves as bytecode, WASM, or LLVM IR:

```
.ecl source
  │
  ├─▶ eclexia-lexer      logos-based; dimensional literals (e.g. 5.0 J, 20 ms)
  ├─▶ eclexia-parser     Pratt parser; macro definitions
  ├─▶ eclexia-ast        syntax tree + visitor framework
  ├─▶ eclexia-typeck     Hindley–Milner, Robinson unification, dimensional analysis
  ├─▶ eclexia-hir        concurrency forms: Spawn, Channel, Send, Recv, Select, Yield
  ├─▶ eclexia-mir        constant propagation, dead-code elimination, block inlining
  └─▶ eclexia-codegen    bytecode (.eclb, serde) ─▶ stack VM
                          │
                          ├─▶ eclexia-wasm       real .wasm via wasm-encoder, WASI preview1
                          ├─▶ eclexia-llvm       textual .ll, links eclexia-rt-native
                          └─▶ eclexia-cranelift  JIT for integer functions
```

A separate tree-walking interpreter (`eclexia-interp`) runs the same AST
directly, with concurrency via tokio. Two execution paths therefore exist —
interpreter and compiled — and they do not agree on macro expansion (see
Known gaps).

## Directory layout

| Path | Contents |
|------|----------|
| `compiler/` | Front end, IRs, backends, and tooling (LSP, DAP, fmt, lint, doc, debugger) |
| `runtime/` | Resource tracking, shadow-price engine, scheduler, profiler, carbon monitor, async, plus service crates (REST, GraphQL, gRPC, registry, web) |
| `stdlib/` | 9 `.ecl` modules: core, collections, math, io, text, time, async, dom, tea |
| `formal/` | Coq (`Typing.v`, `Syntax.v`, `Echo.v`, `EchoThermo.v`, `ShadowPrices.v`) and Agda (`ResourceTracking.agda`) |
| `spec/` | Language specification sources |
| `examples/` | 39 runnable `.ecl` programs |
| `libraries/`, `interop/`, `ffi/` | Bindings and the four validated language bridges |
| `benches/`, `fuzz/`, `.clusterfuzzlite/` | Benchmarks and fuzzing harnesses |
| `.machine_readable/` | Agent-facing metadata (see below) |
| `docs/`, `site/` | Documentation sources, deployed via Ddraig SSG |

The Cargo workspace declares 53 members in total.

## The resource economy

This is what distinguishes Eclexia from a conventional language:

- **Shadow prices** — LP-duality pricing with EMA forecasting; defaults
  `energy=0.000033`, `time=0.001`, `carbon=0.00005`.
- **Adaptive engine** — enforces budgets and selects among candidate solutions.
- **Scheduler** — shadow-price-aware defer / reject / run decisions.
- **Carbon monitor** — grid intensity as Green / Yellow / Red signals.
- **`Echo[A,B]`** — structured information loss as a type former: erasing a
  collapsed fibre's witness is priced through Landauer's principle
  (`landauer_cost(states, T) : Resource[Energy]`), in the same currency as
  energy and carbon. Echo is core, not a plugin — it sits in both the type
  system and the resource economy.

## Machine-readable metadata

Agents should enter at `0-AI-MANIFEST.a2ml`, which declares the read order.
Structured state lives in `.machine_readable/6a2/` (`STATE.a2ml`, `META.a2ml`,
`ECOSYSTEM.a2ml`, `AGENTIC.a2ml`, `NEUROSYM.a2ml`, `PLAYBOOK.a2ml`).
Governance sits alongside in `contractiles/` (Adjust/Bust/Dust/Intent/Must/Trust),
`bot_directives/`, and `self-validating/` (K9/Nickel validators).
`ANCHOR.scm` at the root is the upstream-canonical anchor.

Invariant: `.scm` and metadata files belong in `.machine_readable/`, never at
the repository root.

## Packaging

Guix (`guix.scm`) is the sole supported packaging route. Nix was retired on
2026-05-18 — do not add a `flake.nix`.

## Known gaps

These are real and tracked, not aspirational polish:

- WASM linear memory has a bump allocator defined but not wired; there is no GC.
- LLVM linking to `eclexia-rt-native` is manual, not automated.
- Runtime metrics are not wired to real OS metrics, except RSS memory on Linux.
- Macro expansion diverges between paths: the interpreter expands fully, while
  MIR emits a `__eclexia_macro_expand` runtime intrinsic.
- No measured benchmarks exist; all performance claims are projections.
- `ShadowPrices.v` carries 5 cited LP axioms (weak/strong duality,
  complementary slackness, LP sensitivity, dual simplex convergence). They are
  documented rather than discharged — tracked in issue #43.
- The package registry exists as a server stub and is not deployed.
- A reproducible out-of-memory crash exists in the `fuzz_main` target, found by
  ClusterFuzzLite on 2026-07-26 and not yet fixed.

---

*Last updated: 2026-07-29*
