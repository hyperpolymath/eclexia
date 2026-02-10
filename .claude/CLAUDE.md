## Current Session Status (Updated 2026-02-09)

**Build Status:** 25 crates compiling, 297 lib tests passing, zero warnings
**Panic-Attack:** 15 weak points (331 unwraps, 28 unsafe, 48 panic sites) — scan 2026-02-09 session 6
**Conformance:** 32/32 valid + 19/19 invalid passing (0 skips)
**License:** All files PMPL-1.0-or-later
**Examples:** 11 working .ecl programs in examples/

**Core Compiler Pipeline (WORKING):**
- Lexer (logos, 893 lines, 95+ tokens, 48 keywords) → Parser (Pratt, 3106 lines) → AST
- TypeChecker (Robinson unification, 2210 lines) → HIR lowering → MIR lowering
- Bytecode codegen → Stack-based VM (934 lines, full instruction set) → .eclb serialization (serde)
- Tree-walking interpreter (separate path, 28 builtin tests, extern block stubs)
- `build` command uses full pipeline: Parse → TypeCheck → HIR → MIR → Bytecode (→ .eclb output) or WASM (→ .wasm)
- `build --target wasm` generates real .wasm binary modules via wasm-encoder
- `run` command uses interpreter with type checking
- `run-bytecode` command loads and executes .eclb files
- `debug` command uses full pipeline with interactive debugger

**Developer Tooling:**
- LSP: diagnostics, completion, go-to-def, references, symbols, hover, rename, signature help, formatting
- Formatter (eclexia-fmt): trait, impl, module, effect, static, extern formatting
- Linter (eclexia-lint): configurable lint rules
- Debugger: breakpoints, step, continue, stack/locals/callstack/resources inspection
- Package manager with registry client

**Runtime:** Shadow prices, resource tracking, adaptive decision engine, scheduler, profiler, carbon monitor, shadow price engine
**Standard Library:** core, collections, math, I/O, text, time, async (7 modules, ~1420 lines .ecl)
**Concurrency:** eclexia-async runtime (executor, channel, task, parallel, 10 tests)
**Formal Verification:** Coq/Agda files present (1222 lines, some theorems Admitted)

**Reactive Compiler Infrastructure (STRUCTURAL - not wired into main pipeline):**
- eclexia-db: Salsa incremental compilation database (8 tests)
- eclexia-modules: Module system, dep graph, parallel compilation (21 tests)
- eclexia-comptime: Compile-time evaluation, constant folding (19 tests)
- eclexia-absinterp: Abstract interpretation, interval analysis (38 tests)
- eclexia-effects: Effect system, evidence passing, row polymorphism (26 tests)
- eclexia-specialize: Binding-time analysis, specialization (14 tests)
- eclexia-cranelift: Native backend (real Cranelift JIT for simple int functions, fallback estimation, 8 tests)
- eclexia-llvm: LLVM backend (REAL - generates textual LLVM IR .ll files, 21 tests)
- eclexia-wasm: WebAssembly backend (REAL - generates valid .wasm binaries via wasm-encoder, 15 tests)
- eclexia-tiered: Tiered execution, PGO profiling, watch mode (26 tests)

**Known Gaps:**
- All 3 backends generate real code: WASM (binary .wasm), LLVM (textual .ll IR), Cranelift (JIT for simple functions)
- WASM: no GC/complex types/WASI yet; strings are fixed data section offsets
- LLVM: textual IR only (no llvm-sys); needs `llc` for native compilation; no complex type lowering yet
- Cranelift: only simple integer functions compile to real native code; complex ops fall back to estimation
- Reactive crates not yet wired into CLI commands
- Formal verification has Admitted/unproven theorems

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
