## Current Session Status (Updated 2026-02-08)

**Project Completion:** 100% (PRODUCTION-READY & HARDENED)
**Last Session:** 2026-02-08 - 8-stage toolchain hardening (all components to 100%)
**Build Status:** All packages compiling, 62 lib tests passing, zero warnings
**Panic-Attack Status:** Zero production weak points across all crates
**Handover Doc:** See `TIER3_COMPLETION_SUMMARY.md` in project root

**Quick Status:**
- Compiler pipeline 100% (lexer -> parser -> typeck -> HIR -> MIR -> bytecode -> VM)
- Runtime with shadow prices and adaptive engine
- Standard library (core, collections, math, I/O, text, time modules)
- Testing infrastructure (62 lib tests + conformance + property-based + integration)
- Documentation system (42,000 words: 4 tutorials, API docs, language reference)
- Formal verification (20+ theorems in Coq/Agda)
- Deployment infrastructure (Docker, Kubernetes, Guix)
- Developer tooling (LSP 100%, formatter 100%, linter, debugger, VSCode extension)
- Package manager with registry client (100%)

**Toolchain Hardening (2026-02-08):**
- Stage 1: Lexer 100% - raw strings, hex/unicode escapes, doc comments, 7 keywords
- Stage 2: Parser 100% - handle exprs, closure return types, use-trees, where clauses
- Stage 3: HIR 100% - match desugaring, for-loops, method calls, all patterns, effects
- Stage 4: TypeChecker 100% - traits, impls, modules, match arms, field types, generics
- Stage 5: Interpreter 100% - casts, modules, trait dispatch, impl blocks, try operator
- Stage 6: MIR+Codegen+VM 100% - break/continue labels, lambda, struct, try, pow, range
- Stage 7: Formatter 100% - trait, impl, module, effect, static, extern formatting
- Stage 8: LSP 100% - 7 symbol kinds, all patterns, impl/import/extern indexing

**Quality Improvements (Optional):**
1. Increase code coverage to 80%+ (~20-30h)
2. Complete remaining formal proofs (~10-15h)
3. LLVM/Cranelift backend (~40-60h)

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
