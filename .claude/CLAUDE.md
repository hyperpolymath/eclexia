## Current Session Status (Updated 2026-02-12)

**Build Status:** 25 crates compiling, 507 total tests (446 lib + 32/32 valid + 19/19 invalid conformance), zero clippy warnings, zero failures
**Security:** 20 production unwraps (down from 100+), 28 unsafe blocks (all FFI), 0 clippy warnings
**Conformance:** 32/32 valid + 19/19 invalid passing (0 skips)
**License:** All files PMPL-1.0-or-later
**Examples:** 11 working .ecl programs in examples/
**SONNET-TASKS:** All 18 tasks complete

**Core Compiler Pipeline (WORKING):**
- Lexer (logos, 893 lines, 95+ tokens, 48 keywords) -> Parser (Pratt, 3106 lines) -> AST
- TypeChecker (Robinson unification, 2210 lines) -> HIR lowering (with concurrency: Spawn, Channel, Send, Recv, Select, Yield, MacroCall) -> MIR lowering
- Bytecode codegen (with concurrency builtins) -> Stack-based VM (934 lines, 18 unit tests) -> .eclb serialization (serde)
- Tree-walking interpreter (separate path, 28 builtin tests, concurrency via tokio)
- `build` command uses full pipeline: Parse -> TypeCheck -> HIR -> MIR -> Bytecode (-> .eclb output) or WASM (-> .wasm) or LLVM (-> .ll)
- `build --target wasm` generates real .wasm binary modules via wasm-encoder (complex types as i32 linear memory pointers, WASI preview1 imports)
- `build --target llvm` generates real .ll IR files (with rt-native static library for linking)
- `run` command uses interpreter with type checking
- `run-bytecode` command loads and executes .eclb files
- `debug` command uses full pipeline with interactive debugger

**Developer Tooling:**
- LSP: diagnostics, completion, go-to-def, references, symbols, hover, rename, signature help, formatting
- Formatter (eclexia-fmt): trait, impl, module, effect, static, extern formatting
- Linter (eclexia-lint): 10+ configurable lint rules
- Debugger: breakpoints, step, continue, stack/locals/callstack/resources inspection
- Package manager with dependency resolution + registry server stub
- Interop bridge validator: `eclexia interop check` validates 4 language bridges

**Runtime:** Shadow prices (real defaults: energy=0.000033, time=0.001, carbon=0.00005), resource tracking, adaptive decision engine (7 tests), scheduler (4 tests), profiler with RSS memory (6 tests), carbon monitor (7 tests), shadow price engine with LP duality (8+ tests)
**Standard Library:** core, collections, math, I/O, text, time, async (7 modules, ~1420 lines .ecl)
**Concurrency:** HIR expressions + interpreter (tokio) + VM builtins (task_spawn, task_await, channels)
**Formal Verification:** Typing.v (0 Admitted), ShadowPrices.v (4 Admitted — deep LP theory), ResourceTracking.agda

**Backends (All 3 generate real code):**
- **WASM:** Valid .wasm binaries via wasm-encoder; complex types (tuples, arrays, structs) as i32 linear memory pointers; WASI preview1 imports (fd_write, clock_time_get, args); 24 tests
- **LLVM:** Textual .ll IR files; runtime linking via eclexia-rt-native static library (5 C-compatible symbols); 21 tests
- **Cranelift:** Real JIT for simple integer functions; string data sections; Range/RangeInclusive support; fallback estimation for complex ops; 8 tests

**Reactive Compiler Infrastructure (STRUCTURAL - wired into --analyze):**
- eclexia-db: Salsa incremental compilation database (8 tests)
- eclexia-modules: Module system, dep graph, parallel compilation (21 tests)
- eclexia-comptime: Compile-time evaluation, constant folding (19 tests)
- eclexia-absinterp: Abstract interpretation, interval analysis (38 tests)
- eclexia-effects: Effect system, evidence passing, row polymorphism (26 tests)
- eclexia-specialize: Binding-time analysis, specialization (14 tests)
- eclexia-cranelift: Native backend (real Cranelift JIT, 8 tests)
- eclexia-llvm: LLVM backend (real .ll generation, 21 tests)
- eclexia-wasm: WebAssembly backend (real .wasm binaries, 24 tests)
- eclexia-tiered: Tiered execution, PGO profiling, watch mode (26 tests)

**Known Gaps (honest):**
- WASM: no GC in linear memory (bump allocator defined but not wired)
- LLVM: linking to runtime is manual (static library exists, automatic linking not wired)
- Runtime metrics not wired to real OS metrics (except RSS memory on Linux)
- Macro expansion: MacroCall lowered to HIR but MIR emits Nop (only interpreter supports macro eval)
- No measured benchmarks (all performance claims are projections)
- Package registry server stub exists but not deployed
- 4 Admitted in ShadowPrices.v (strong duality, dual variables, complementary slackness)

---

## Machine-Readable Artefacts

The following files in `.machine_readable/` contain structured project metadata:

- `STATE.scm` - Current project state and progress
- `META.scm` - Architecture decisions and development practices
- `ECOSYSTEM.scm` - Position in the ecosystem and related projects
- `AGENTIC.scm` - AI agent interaction patterns
- `NEUROSYM.scm` - Neurosymbolic integration config
- `PLAYBOOK.scm` - Operational runbook

---

# CLAUDE.md - AI Assistant Instructions

## Language Policy (Hyperpolymath Standard)

### ALLOWED Languages & Tools

| Language/Tool | Use Case | Notes |
|---------------|----------|-------|
| **ReScript** | Primary application code | Compiles to JS, type-safe |
| **Deno** | Runtime & package management | Replaces Node/npm/bun |
| **Rust** | Performance-critical, systems, WASM | Preferred for CLI tools |
| **Tauri 2.0+** | Mobile apps (iOS/Android) | Rust backend + web UI |
| **Dioxus** | Mobile apps (native UI) | Pure Rust, React-like |
| **Gleam** | Backend services | Runs on BEAM or compiles to JS |
| **Bash/POSIX Shell** | Scripts, automation | Keep minimal |
| **JavaScript** | Only where ReScript cannot | MCP protocol glue, Deno APIs |
| **Nickel** | Configuration language | For complex configs |
| **Guile Scheme** | State/meta files | STATE.scm, META.scm, ECOSYSTEM.scm |
| **Julia** | Batch scripts, data processing | Per RSR |
| **OCaml** | AffineScript compiler | Language-specific |
| **Ada** | Safety-critical systems | Where required |

### BANNED - Do Not Use

| Banned | Replacement |
|--------|-------------|
| TypeScript | ReScript |
| Node.js | Deno |
| npm | Deno |
| Bun | Deno |
| pnpm/yarn | Deno |
| Go | Rust |
| Python | Julia/Rust/ReScript |
| Java/Kotlin | Rust/Tauri/Dioxus |
| Swift | Tauri/Dioxus |
| React Native | Tauri/Dioxus |
| Flutter/Dart | Tauri/Dioxus |

### Mobile Development

**No exceptions for Kotlin/Swift** - use Rust-first approach:

1. **Tauri 2.0+** - Web UI (ReScript) + Rust backend, MIT/Apache-2.0
2. **Dioxus** - Pure Rust native UI, MIT/Apache-2.0

Both are FOSS with independent governance (no Big Tech).

### Enforcement Rules

1. **No new TypeScript files** - Convert existing TS to ReScript
2. **No package.json for runtime deps** - Use deno.json imports
3. **No node_modules in production** - Deno caches deps automatically
4. **No Go code** - Use Rust instead
5. **No Python anywhere** - Use Julia for data/batch, Rust for systems, ReScript for apps
6. **No Kotlin/Swift for mobile** - Use Tauri 2.0+ or Dioxus

### Package Management

- **Primary**: Guix (guix.scm)
- **Fallback**: Nix (flake.nix)
- **JS deps**: Deno (deno.json imports)

### Security Requirements

- No MD5/SHA1 for security (use SHA256+)
- HTTPS only (no HTTP URLs)
- No hardcoded secrets
- SHA-pinned dependencies
- SPDX license headers on all files
