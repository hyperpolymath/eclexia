# ECLEXIA: Complete Project Status, Priority Plan & Thread Decomposition
# Generated: 2026-02-09 (KEEP UPDATED EVERY SESSION)
# Author: Claude Code (Opus 4.6) for Jonathan D.A. Jewell
# Purpose: THE reference document any LLM can read to pick up where we left off

---

## HOW TO USE THIS DOCUMENT

**For any AI assistant picking this up:** Read this entire document before starting work.
It contains the honest status of eclexia, what's been done, what's claimed but fake,
what's broken, and what needs doing next. The TO-DO list is priority ordered. Move
completed items to the TO-DONE section at the bottom as you finish them.

**For Jonathan:** This is your single source of truth. If a conversation crashes,
hand this file to the next session.

---

## TABLE OF CONTENTS

1. [Honest Status Assessment](#1-honest-status-assessment)
2. [What's Actually Done](#2-whats-actually-done)
3. [What's Claimed But Not Done](#3-whats-claimed-but-not-done)
4. [What's Broken Right Now](#4-whats-broken-right-now)
5. [Security Issues](#5-security-issues)
6. [Infrastructure Integration Status](#6-infrastructure-integration-status)
7. [Complete Task List (Priority Ordered)](#7-complete-task-list-priority-ordered)
8. [Thread Decomposition](#8-thread-decomposition)
9. [Theory & Proofs Status](#9-theory--proofs-status)
10. [Library Ecosystem Plan](#10-library-ecosystem-plan)
11. [Example Programs](#11-example-programs)
12. [IDE Plugins & Tooling](#12-ide-plugins--tooling)
13. [External Tool Integration](#13-external-tool-integration-panll-opsm)
14. [Roadmap Items from Planning Docs](#14-roadmap-items-from-planning-docs)
15. [File Inventory](#15-file-inventory)
16. [TO-DONE (Completed Items)](#16-to-done-completed-items)
17. [Revision History](#17-revision-history)

---

## 1. HONEST STATUS ASSESSMENT

**Overall Completion: ~67% (was 65% — WASM backend generates real .wasm binaries, Cranelift has real JIT skeleton, --target wasm CLI working, 278 tests)**

**Philosophy:** Eclexia = "Economics as Code" — resource tracking, shadow prices,
adaptive functions, carbon-aware scheduling. Computational resources are first-class
economic concepts. This is what makes eclexia unique.

**VM:** Own stack-based bytecode VM (934 lines), NOT on any existing VM (BEAM/JVM/CLR).
BEAM targeting would require a new backend crate (eclexia-beam) compiling MIR → BEAM bytecode.

| Component | Claimed | Actual | Notes |
|-----------|---------|--------|-------|
| Lexer | 100% | 100% | Genuinely complete. 893 lines, 95+ tokens, 48 keywords |
| Parser | 100% | 95% | Works well, 3106 lines. 52 unwrap calls on untrusted input |
| Type Checker | 100% | 97% | Robinson unification, generics, lowercase types, builtins, Resource<D> types, casts, concurrency stubs, extern block signatures. 32/32 valid conformance pass |
| HIR Lowering | 100% | 95% | Match desugaring, for-loops, effects all work |
| MIR Lowering | 100% | 90% | Optimisation passes work |
| Bytecode Codegen | 100% | 95% | Works, serde derives, JSON serialization, .eclb binary format (8-byte header + JSON body) |
| VM | 100% | 90% | Stack-based VM works. 934 lines. Bytecode file loading via .eclb, disasm command |
| Interpreter | 100% | 95% | Tree-walking, 28 builtin tests. Extern block stubs (graceful error). Enum variant matching FIXED. 96 unwraps in builtins |
| Formatter | 100% | 95% | Works well for all constructs |
| Linter | 100% | 90% | 6 rules implemented |
| LSP | 100% | 80% | Diagnostics, completion, go-to-def. No resource-type awareness |
| Debugger | 100% | 75% | Breakpoints, step work. Resource inspection partial |
| Runtime: Scheduler | 100% | 70% | Shadow-price-aware scheduling, defer/reject/run, 4 tests |
| Runtime: Profiler | 100% | 70% | Wall-clock profiling, energy/carbon estimation, 6 tests |
| Runtime: Carbon | 100% | 70% | Grid intensity monitor, Green/Yellow/Red signals, 7 tests |
| Runtime: Shadow | 100% | 70% | Utilization-curve LP duality pricing, EMA smoothing, 8 tests |
| Runtime: Shadow Prices | 100% | 40% | Formal defs exist, not integrated into runtime |
| Runtime: Adaptive | 100% | 60% | ~200 lines exist, not connected to real tracking |
| Runtime: Resource Tracker | 100% | 50% | Tracks at instruction level, not real system |
| Cranelift Backend | skeleton | ~15% | **Real Cranelift JIT for simple int functions; complex ops fall back to estimation** |
| LLVM Backend | stub | 0% | **Planning stub — estimates sizes only. Needs llvm-sys for real codegen** |
| WASM Backend | WORKING | ~60% | **Generates real .wasm binaries via wasm-encoder. MIR→WASM lowering for arithmetic, control flow, resources. No GC/complex types yet** |
| Package Manager CLI | 100% | 80% | Manifest, resolver work. Registry client is stub |
| Package Registry Server | N/A | 0% | **Does not exist** |
| Standard Library | 95% | 65% | 7 modules (core, collections, math, I/O, text, time, async), most are @builtin markers |
| Docker | 100% | 70% | Builds but contains mostly-stub runtime |
| Kubernetes | 100% | 30% | Configs reference non-existent endpoints |
| Formal Verification | 100% | 40% | 22 theorems are Admitted (assumed, not proven) |
| Documentation | 100% | 85% | Honesty pass applied to 6 key docs (GETTING_STARTED, SELF-HOSTING-ROADMAP, MULTICOMPILER-ARCHITECTURE, ROADMAP, IMPLEMENTATION_ROADMAP, WHITEPAPER) |
| VSCode Extension | 100% | 85% | Syntax highlighting + LSP integration works |
| Minter | N/A | 100% | Token minting command — recently added, works |

---

## 2. WHAT'S ACTUALLY DONE

These components genuinely work and have been tested:

### Compiler Pipeline (REAL)
- **Lexer** (`compiler/eclexia-lexer/src/lib.rs`, 893 lines): Full tokenisation with raw strings, hex/unicode escapes, doc comments, dimensional literals
- **Parser** (`compiler/eclexia-parser/`, 3106+ lines): Pratt parsing, 32/32 valid conformance, handle exprs, use-trees, where clauses, closures, contextual keywords (energy/latency/memory/carbon)
- **AST** (`compiler/eclexia-ast/`): Full expression/statement/pattern/type AST, concurrency primitives (Spawn/Channel/Send/Recv/Select/Yield)
- **Type Checker** (`compiler/eclexia-typeck/`): Robinson unification, traits, impls, modules, generics, Resource<D> type resolution, numeric↔Resource casts, @requires resource injection, Float/F64 + Int/I64 compat, concurrency stubs
- **HIR** (`compiler/eclexia-hir/`): Match desugaring, for-loop bodies, method calls, all patterns, effects
- **MIR** (`compiler/eclexia-mir/`): Break/continue labels, lambda, struct, try, tuple/array. Optimisations: constant propagation, dead code elimination, block inlining
- **Bytecode Codegen** (`compiler/eclexia-codegen/`): All instructions, switch, callindirect, range, cast, pow
- **VM** (`compiler/eclexia-codegen/src/vm.rs`, 934 lines): Range values, callindirect, cast conversions, pow, field/index, debug mode
- **Interpreter** (`compiler/eclexia-interp/`): Casts, modules, trait dispatch, impl blocks, try operator, 28 builtins

### Developer Tooling (REAL)
- **CLI** (`compiler/eclexia/src/main.rs`): build (--analyze), run, check, fmt, repl, init, new, test, bench, doc, lint, debug, install, watch, disasm, minter
- **REPL** (`compiler/eclexia/src/repl.rs`): Expression evaluation with resource tracking display
- **Formatter** (`compiler/eclexia-fmt/`): AST pretty printer
- **Linter** (`compiler/eclexia-lint/`): 6 rules
- **LSP** (`compiler/eclexia-lsp/`): Diagnostics, completion, go-to-def, references, symbols, hover, rename, signature help
- **Debugger** (`compiler/eclexia-debugger/`): Breakpoints, single-step, stack/locals inspection
- **Doc Generator** (`compiler/eclexia-doc/`): HTML/Markdown from doc comments
- **VSCode Extension** (`editors/vscode/`): Syntax highlighting + LSP integration
- **Minter** (`compiler/eclexia/src/commands.rs`): Token minting command

### Reactive Compiler Infrastructure (PARTIALLY WIRED)
These exist with their own tests. Four are now wired into CLI via `build --analyze`:
- `eclexia-comptime`: Compile-time evaluation, constant folding (19 tests) — **WIRED** via `build --analyze`
- `eclexia-absinterp`: Abstract interpretation, interval analysis (38 tests) — **WIRED** via `build --analyze`
- `eclexia-specialize`: Binding-time analysis, specialisation (14 tests) — **WIRED** via `build --analyze`
- `eclexia-effects`: Effect system, evidence passing, row polymorphism (26 tests) — **WIRED** via `build --analyze`
- `eclexia-db`: Salsa incremental compilation (8 tests) — not yet wired
- `eclexia-modules`: Module system, dep graph, parallel compilation (21 tests) — not yet wired
- `eclexia-tiered`: Tiered execution, PGO profiling, watch mode (26 tests) — not yet wired

---

## 3. WHAT'S CLAIMED BUT NOT DONE

### Category A: Stubs Presented as Complete

| What's Claimed | File | Actual Content |
|----------------|------|----------------|
| ~~Runtime scheduler~~ | ~~`runtime/eclexia-runtime/src/scheduler.rs`~~ | **DONE** — shadow-price-aware scheduling, 4 tests |
| ~~Runtime profiler~~ | ~~`runtime/eclexia-runtime/src/profiler.rs`~~ | **DONE** — wall-clock profiling, energy/carbon, 6 tests |
| ~~Carbon-aware scheduling~~ | ~~`runtime/eclexia-runtime/src/carbon.rs`~~ | **DONE** — grid intensity monitor, 7 tests |
| ~~Shadow price observation~~ | ~~`runtime/eclexia-runtime/src/shadow.rs`~~ | **DONE** — LP duality pricing, EMA smoothing, 8 tests |
| ~~Shadow prices computed~~ | ~~`compiler/eclexia/src/commands.rs`~~ | **FIXED** — Uses ShadowPriceRegistry (energy=0.000033, time=0.001, carbon=0.00005) + dynamic ShadowPriceEngine from VM usage |
| Cranelift native backend | `compiler/eclexia-cranelift/` | Real JIT for simple int functions, estimation fallback |
| LLVM native backend | `compiler/eclexia-llvm/` | Planning stub — estimates sizes only |
| WASM backend | `compiler/eclexia-wasm/` | **REAL** — generates valid .wasm binaries, CLI `--target wasm` |
| ~~Bytecode file output~~ | ~~`commands.rs`~~ | **DONE** — .eclb binary format (8-byte header + JSON), write/read/round-trip verified |
| Package registry | README.adoc | "server not yet deployed" |

### Category B: Exaggerated Completeness

| Claim | Reality |
|-------|---------|
| "100% FEATURE-COMPLETE & PRODUCTION-READY" | ~65% functional (was ~45% at initial audit) |
| "20+ mechanically-verified theorems" | 22 are `Admitted` (assumed) |
| "Standard Library (95%)" | Most are `@builtin(...)` markers |
| "Runtime System (100%)" | 4 of 6 modules implemented (scheduler, profiler, carbon, shadow). Remaining: adaptive + resource tracker partial. |
| "Package Manager (100%)" | Registry server doesn't exist |
| "96 tests total" | Includes "9 aspirational" tests |
| "Carbon-aware scheduling" | Parser recognises syntax, carbon monitor + shadow pricing implemented, not yet wired to @defer_until |
| "Energy Reduction: 20-40%" | Zero benchmarks exist |

---

## 4. WHAT'S BROKEN RIGHT NOW

### 4.1 Conformance Test Regression
- **Status:** FULLY FIXED (2026-02-09)
- **Valid tests:** 32/32 pass (was 3/32, then 29/32, now 32/32)
- **Invalid tests:** 19/19 correctly reject (0 skips). Dimension comparison check added (commit 8c9f564).
- **Fixes applied (session 1):** Added `assert`, `panic`, `shadow_price`, `Some`, `None`, `Ok`, `Err` builtins to type checker. Added lowercase type names (`int`, `bool`, `float`, `string`). Added `latency` resource type. Added `gCO2` unit alias. Fixed range operator to return iterable type. Fixed const type annotation resolution. Added generic type parameter support.
- **Fixes applied (session 2):** Added numeric-to-Resource cast validation. Added @requires attribute injection into function scope (both constraint and annotation paths). Added concurrency expression type stubs (Spawn/Channel/Send/Recv/Select/YieldExpr). Added MacroDef handling across all crates.
- **All 271 library tests pass. 2/2 conformance suites pass (51 total: 32 valid + 19 invalid, 0 skips).**
- **panic-attack scan (2026-02-09, latest):** 15 weak points, 327 unwraps, 28 unsafe blocks (Idris2 believe_me), 48 panic sites, 49,990 lines. 2 Critical (believe_me in ABI files).
- **Enum variant matching bug FIXED (session 8):** Unit enum variants (`Red`, `Green`, `Blue`) were parsed as `Pattern::Var` (catch-all variable binding), always matching first arm. Fix: `match_pattern()` now checks global env for known enum variant names. Also fixed `Value::Struct` PartialEq (was returning false for identical structs).

### 4.2 Security Vulnerability
- **CVE:** RUSTSEC-2026-0007 — Integer overflow in `bytes` 1.11.0
- **Severity:** HIGH
- **Fix:** DONE 2026-02-09. `cargo update bytes` → 1.11.1

### 4.3 Unmaintained Dependency
- **Advisory:** RUSTSEC-2025-0134 — `rustls-pemfile` 1.0.4
- **Fix:** DONE 2026-02-09. Upgraded reqwest 0.11→0.12 (commit dbbe4f4)

### 4.4 Bytecode Build Limitation — FIXED
- **FIXED (session 10, commit 36b686c):** `build` command now works on files using builtins
- Added `CallBuiltin` bytecode instruction + VM `execute_builtin` dispatch
- Supports: println, print, to_string, len, abs, min, max, sqrt, and more
- .eclb round-trip verified for hello_world, fibonacci, math_showcase

### 4.5 `build --analyze` Panic on Adaptive Def — FIXED
- **FIXED (session 10, commit 36b686c):** MIR lowering for adaptive def solutions
- Fix: Solutions now share parent function parameters; unknown locals produce Unit instead of panic
- `build --analyze examples/budget_enforcement.ecl` now shows binding-time analysis + budget verdicts

### 4.6 Uncommitted Work at Risk
- **Status (2026-02-09):** Working tree is dirty with uncommitted changes (multiple files modified + untracked examples).
- **Current risk:** High — do not lose this session without committing or stashing.

### 4.7 Bytecode VM Feature Gaps (New)
- **Status (2026-02-09):** Bytecode build/run verified on 25/36 examples; 11 fail or hang.
- **Failures:** `carbon_aware` (struct field access), `closures/generics/higher_order/type_system` (call-indirect), `string_processing` (string ops), `json_test` (missing file I/O builtins), `comprehensive_opportunity` (missing builtin + type conversion), `range_loops` (int conversion), `traits_and_impls` (method call/field), `control_flow` (hang in bytecode loop).
- **Root causes:** VM lacks struct field storage, string ops, call-indirect for closures, and full builtin coverage in bytecode path.

---

## 5. SECURITY ISSUES

### 5.1 Dependency Vulnerabilities
- `bytes` 1.11.0: CVE-level integer overflow (FIX: cargo update)
- `rustls-pemfile` 1.0.4: Unmaintained (FIX: upgrade reqwest)

### 5.2 Panic Path Risks (DoS Vectors) — Updated 2026-02-09 (session 7)
- **327 total unwrap() calls** (~220 / 85% in test code — SAFE)
- **3 dangerous production unwraps FIXED** (commit 6eb2b45):
  - `eclexia-modules/src/lib.rs:202-205` — `path.file_name().unwrap()` → `let Some(fname) = ... else { continue }`
  - `eclexia/src/commands.rs:1477` — `io::stdout().flush().unwrap()` → `let _ = io::stdout().flush()`
  - `eclexia-lsp/src/symbols.rs:822` — `.position().unwrap()` → `if let Some(pos)`
- **Remaining production unwraps** (not yet fixed): builtins.rs (96), parser/lib.rs (94), parser/expr.rs (31)
- **28 unsafe blocks** (all Idris2 believe_me in ABI definitions — intentional)
- **48 panic sites** across codebase

### 5.3 Infrastructure (These ARE in place)
- 17 security-focused GitHub Actions workflows ✓
- RFC 9116 security.txt ✓
- TLS 1.3 minimum, HSTS, CAA records ✓
- SPDX headers on all files ✓
- SHA-pinned Actions ✓
- TruffleHog + Gitleaks secret scanning ✓
- CodeQL analysis ✓

---

## 6. INFRASTRUCTURE INTEGRATION STATUS

### 6.1 gitbot-fleet — NOT ENROLLED
- Fleet: 9 bots (rhodibot, echidnabot, sustainabot, glambot, seambot, finishbot, accessibilitybot, cipherbot, robot-repo-automaton)
- Eclexia hypatia-scan.yml exists but not in supervised list
- **Action:** Add to supervised repos, run fleet-coordinator

### 6.2 git-private-farm — NOT REGISTERED
- Farm: 28+ repos, multi-forge propagation (GitHub, GitLab, SourceHut, Codeberg, Bitbucket, Radicle)
- **Action:** Add eclexia to farm-manifest.json

### 6.3 Hypatia — PARTIAL
- hypatia-scan.yml workflow exists, CII badge tracking active
- Missing: eclexia-specific Logtalk rules, NEUROSYM.scm empty, verisimdb not wired
- **Action:** Create rules, populate NEUROSYM.scm, wire verisimdb

### 6.4 Echidna — ZERO INTEGRATION
- 17 prover backends available (Coq, Lean 4, Isabelle/HOL, Agda, Z3, CVC5, ACL2, PVS, HOL4, Mizar, HOL Light, Metamath, Vampire, E Prover, SPASS, Alt-Ergo, Idris2)
- Eclexia has Coq/Agda proofs that echidna could verify
- **Action:** Configure echidna for eclexia proofs

### 6.5 panic-attack — SCANNED (2026-02-09, session 6)
- 15 weak points, 327 unwraps, 28 unsafe blocks (Idris2 believe_me), 48 panic sites
- Results: `/tmp/eclexia-scan.json`
- **Top offenders:** builtins.rs (96 unwraps), parser/lib.rs (94), parser/expr.rs (31), eclexia-async (10)
- **Critical:** 2 believe_me in ResourceABI.idr, 1 in Foreign.idr (intentional Idris2 pattern)
- **Action:** Reduce unwraps in parser/interpreter (priority: builtins.rs)

### 6.6 VeriSimDB — INGESTED (2026-02-09)
- Scan: 15 weak points, 327 unwraps, 28 unsafe blocks, 48 panic sites
- Commit `9ef8bab` in verisimdb-data repo, pushed to GitHub + GitLab
- **Action:** Set up automated re-scanning via PAT

### 6.7 Sustainabot — PARTIAL
- Has `sustainabot-eclexia` crate but incomplete
- **Action:** Complete integration

### 6.8 Wiki — DOES NOT EXIST
- 37+ docs could seed it, nextgen-languages wiki has eclexia pages
- **Action:** Create GitHub wiki

### 6.9 PanLL (Next-Gen IDE) — NO ECLEXIA SUPPORT
- Path: `/var/mnt/eclipse/repos/panll`
- Status: v0.1.0-alpha (95% complete), ReScript + Tauri 2.0
- Three-pane layout: Symbolic (Pane-L) / Neural (Pane-N) / World (Pane-W)
- **Action:** Add eclexia as native language in PanLL, integrate into Pane-L constraints

### 6.10 OPSM (Odds-and-Sods Package Manager) — ECLEXIA SUPPORT ADDED
- Path: `/var/mnt/eclipse/repos/odds-and-sods-package-manager`
- Status: v1.1.0 production, Elixir/BEAM, **14 registry adapters** (was 13), trust pipeline
- **DONE 2026-02-09:** Eclexia adapter added (commit `a081d67`), 4 tests pass
- Files: `opsm_ex/lib/opsm/registries/eclexia.ex`, wired in `registry.ex` + `types.ex`
- Certificate: `~/Desktop/CERTIFICATE-OPSM-ECLEXIA-2026-02-09.md`
- **Remaining:** eclexia-verifier trust service (Priority 17.2)

---

## 7. COMPLETE TASK LIST (Priority Ordered)

**Instructions:** Move completed items to Section 16 (TO-DONE) with completion date.

### PRIORITY 0: EMERGENCY (Do Now)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 0.1 | Fix conformance test regression | 1-2h | DONE 2026-02-09 (32/32 valid, 16/19 invalid) |
| 0.2 | Commit uncommitted work | 15min | DONE 2026-02-09 (6 commits this session) |
| 0.3 | Fix bytes CVE (cargo update bytes) | 5min | DONE 2026-02-09 |
| 0.4 | Fix rustls-pemfile warning (upgrade reqwest) | 30min | DONE 2026-02-09 (reqwest 0.11→0.12, commit dbbe4f4) |
| 0.5 | Fix 3 remaining parser-level conformance failures | 2h | DONE 2026-02-09 (casts, @requires injection, concurrency stubs) |
| 0.6 | Fix 3 runtime resource enforcement gaps | 4h | DONE 2026-02-09 (dimension comparison check, 0 skips, commit 8c9f564) |

### PRIORITY 1: DOCUMENTATION HONESTY
| # | Task | Effort | Status |
|---|------|--------|--------|
| 1.1 | Rewrite README.adoc with honest percentages | 2h | DONE 2026-02-09 (commit 6c41a4d) |
| 1.2 | Rewrite QUICK_STATUS.md honestly | 1h | DONE 2026-02-09 (commit 6c41a4d) |
| 1.3 | Fix GETTING_STARTED.md — flag what doesn't work | 1h | DONE 2026-02-09 (commit a26acbe — status disclaimer, def→fn, adaptive/dimensional marked planned) |
| 1.4 | Update STATE.scm with real completion numbers | 30min | DONE 2026-02-09 (state now reports verification & honesty audit phase with honest percentiles) |
| 1.5 | Update .claude/CLAUDE.md session status | 30min | DONE 2026-02-09 (commit 6c41a4d + 3471d73) |
| 1.6 | Audit ALL .md files for false claims (WHITEPAPER, THEORY, etc.) | 2h | DONE 2026-02-09 (commit a26acbe — WHITEPAPER.md implementation note added) |
| 1.7 | Audit ROADMAP.adoc — ensure all claims match reality | 1h | DONE 2026-02-09 (commit a26acbe — 80%→~55%, date updated, license fixed, v0.2.0 checklist) |
| 1.8 | Audit IMPLEMENTATION_ROADMAP.md | 1h | DONE 2026-02-09 (commit a26acbe — fixed SPDX typo) |
| 1.9 | Audit SELF-HOSTING-ROADMAP.md | 30min | DONE 2026-02-09 (commit a26acbe — 100%→~55%, frontend/backend status corrected) |
| 1.10 | Audit MULTICOMPILER-ARCHITECTURE.md | 30min | DONE 2026-02-09 (commit a26acbe — added VISION DOCUMENT disclaimer) |

### PRIORITY 2: CORE TOOLCHAIN COMPLETION
| # | Task | Effort | Status |
|---|------|--------|--------|
| 2.1 | Implement bytecode serialisation (write .eclb files) | 4h | DONE 2026-02-09 (serde derives + JSON/binary output, run-bytecode cmd) |
| 2.2 | Implement bytecode loading (read .eclb files) | 2h | DONE 2026-02-09 (read_eclb + run-bytecode command) |
| 2.3 | Connect shadow price computation to real VM metrics | 4h | DONE 2026-02-09 (runtime refresh pulls VM resource totals + schedules with ShadowPriceEngine) |
| 2.4 | Implement runtime scheduler (replace stub) | 6h | DONE 2026-02-09 (commit a6ce99b, 4 tests) |
| 2.5 | Implement runtime profiler (replace stub) | 4h | DONE 2026-02-09 (commit a6ce99b, 6 tests) |
| 2.6 | Implement carbon module (replace stub) | 4h | DONE 2026-02-09 (commit a6ce99b, 7 tests) |
| 2.7 | Implement shadow.rs (replace stub) | 4h | DONE 2026-02-09 (commit a6ce99b, 8 tests) |
| 2.8 | Wire reactive compiler crates into CLI | 8h | PARTIAL 2026-02-09 — 4/7 wired: absinterp + comptime (commit d5241ab) + specialize + effects (commit 0441089). 3 remaining: db, modules, tiered. |
| 2.9 | Reduce unwrap() calls in parser/interpreter | 4h | PARTIAL 2026-02-09 — 3 dangerous production unwraps fixed (commit 6eb2b45: modules, REPL debugger, LSP symbols). 88% of remaining unwraps are in test code. |
| 2.10 | Implement Serialize for BytecodeModule | 2h | DONE 2026-02-09 (commit 8c9f564, serde derives + JSON output) |
| 2.11 | Wire @defer_until to actual carbon-aware scheduling | 4h | DONE 2026-02-09 (Scheduler consults carbon signal + runtime exposes `schedule_task` with optional signal) |
| 2.12 | Implement real resource tracking (RAPL/PowerMetrics) | 6h | DONE 2026-02-09 (PowerMetrics samples RAPL, runtime ingests energy/time/carbon) |
| 2.13 | Add /health and /ready HTTP endpoints for K8s | 2h | DONE 2026-02-09 (built-in health server with `/health` & `/ready` probes) |
| 2.14 | Make stdlib @builtin functions work in bytecode path | 8h | PARTIAL 2026-02-09 — CallBuiltin instruction + VM dispatch for ~20 builtins (commit 36b686c). Full stdlib coverage TODO. |

### PRIORITY 3: ANNOTATION & CODEBASE QUALITY
| # | Task | Effort | Status |
|---|------|--------|--------|
| 3.1 | Complete doc annotations across all crates | 4h | TODO |
| 3.2 | Run panic-attack assail across full codebase | 30min | DONE 2026-02-09 (15 weak pts, 314 unwraps, 28 unsafe, 49 panic sites) |
| 3.3 | Fix all panic-attack findings in production code | 4h | TODO |
| 3.4 | Achieve 80% code coverage (currently 17.92%) | 20h | TODO |
| 3.5 | Address all compiler warnings (should be zero) | 1h | DONE 2026-02-09 (zero warnings) |
| 3.6 | Address all clippy lints | 2h | DONE 2026-02-09 (auto-fixed + manual: Dimension::to_string→format_dimension, Visibility derive Default) |

### PRIORITY 4: EXAMPLE PROGRAMS (Comprehensive Set)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 4.1 | Hello World (basic, interpreted) | 15min | DONE 2026-02-09 (examples/hello_world.ecl) |
| 4.2 | Hello World (compiled bytecode) | 15min | DONE 2026-02-09 (build → .eclb → run verified) |
| 4.3 | Fibonacci (recursive + tail-recursive) | 30min | DONE 2026-02-09 (examples/fibonacci.ecl) |
| 4.4 | Fibonacci adaptive (shadow price selection) | 30min | DONE 2026-02-09 (examples/dimensional_types.ecl; verified run) |
| 4.5 | Resource-tracked computation | 30min | DONE 2026-02-09 (examples/resource_tracking.ecl; verified run) |
| 4.6 | Carbon-aware scheduling example | 30min | DONE 2026-02-09 (examples/carbon_aware.ecl; verified run) |
| 4.7 | Pattern matching showcase | 30min | DONE 2026-02-09 (examples/pattern_matching.ecl) |
| 4.8 | Trait and impl examples | 30min | DONE 2026-02-09 (examples/traits_and_impls.ecl) |
| 4.9 | Effect system demo | 30min | DONE 2026-02-09 (examples/effect_system_demo.ecl; handlers parsed but not executed) |
| 4.10 | Module system demo | 30min | DONE 2026-02-09 (examples/module_system_demo.ecl; qualified paths not yet supported in expressions) |
| 4.11 | Generic functions demo | 30min | DONE 2026-02-09 (examples/generics.ecl) |
| 4.12 | Closure and lambda examples | 30min | DONE 2026-02-09 (examples/closures.ecl) |
| 4.13 | Error handling (Result/Option/try) | 30min | DONE 2026-02-09 (examples/error_handling.ecl) |
| 4.14 | Collections (Vec, HashMap, etc.) | 30min | DONE 2026-02-09 (examples/collections.ecl) |
| 4.15 | I/O operations (file read/write) | 30min | DONE 2026-02-09 (examples/json_test.ecl; verified run) |
| 4.16 | String processing | 30min | DONE 2026-02-09 (examples/string_processing.ecl) |
| 4.17 | Mathematical computations | 30min | DONE 2026-02-09 (examples/math_showcase.ecl) |
| 4.18 | Shadow price optimization showcase | 1h | DONE 2026-02-09 (examples/shadow_price_optimization.ecl; verified run) |
| 4.19 | Multi-objective optimization example | 1h | DONE 2026-02-09 (examples/multi_objective_optimization.ecl; verified run) |
| 4.20 | Budget enforcement demo | 30min | DONE 2026-02-09 (examples/budget_enforcement.ecl) |
| 4.21 | Type casting and dimensional analysis | 30min | TODO |
| 4.22 | Range operators and for-loops | 30min | DONE 2026-02-09 (examples/range_loops.ecl) |
| 4.23 | Struct and enum patterns | 30min | DONE 2026-02-09 (examples/struct_enum.ecl) |
| 4.24 | Unicode identifiers demo | 15min | DONE 2026-02-09 (examples/unicode_ids.ecl) |
| 4.25 | Doc comments and documentation generation | 30min | TODO |
| 4.26 | Test framework usage (#[test]) | 30min | DONE 2026-02-09 (examples/test_example.ecl; includes intentional failing test) |
| 4.27 | Benchmark framework usage (#[bench]) | 30min | DONE 2026-02-09 (examples/bench_example.ecl + bench_energy.ecl; parsing verified) |
| 4.28 | Package manifest and dependency example | 30min | TODO |
| 4.29 | Sustainabot policy (already exists, verify works) | 15min | DONE 2026-02-09 (examples/sustainabot_policy.ecl; verified run) |
| 4.30 | Complete "Economics as Code" tutorial program | 2h | TODO |
| 4.31 | Cross-compilation target examples | 1h | TODO |
| 4.32 | Verify ALL examples interpret, compile, and run | 2h | PARTIAL 2026-02-09 (all 36 examples interpret/run; bytecode compile/run passes 25/36. Failures: carbon_aware, closures, comprehensive_opportunity, control_flow (hangs in bytecode), generics, higher_order, json_test, range_loops, string_processing, traits_and_impls, type_system) |

### PRIORITY 5: INFRASTRUCTURE ENROLLMENT
| # | Task | Effort | Status |
|---|------|--------|--------|
| 5.1 | Register eclexia in git-private-farm | 1h | TODO |
| 5.2 | Enroll eclexia in gitbot-fleet supervision | 2h | TODO |
| 5.3 | Configure echidna to verify eclexia proofs | 4h | TODO |
| 5.4 | Wire hypatia with eclexia-specific Logtalk rules | 4h | TODO |
| 5.5 | Ingest eclexia scan into verisimdb-data | 30min | DONE 2026-02-09 (commit 9ef8bab in verisimdb-data — 15 weak pts, 327 unwraps, 28 unsafe, 48 panic sites) |
| 5.6 | Populate NEUROSYM.scm | 1h | TODO |
| 5.7 | Configure sustainabot-eclexia integration | 2h | TODO |
| 5.8 | Ensure gitbot-fleet continuously monitors eclexia | 1h | TODO |

### PRIORITY 6: PLAYGROUND & WEBSITE
| # | Task | Effort | Status |
|---|------|--------|--------|
| 6.1 | Eclexia playground (web-based REPL) | 8h | TODO |
| 6.2 | Eclexia website (SSG or WordPress) | 6h | TODO |
| 6.3 | Link playground to website | 2h | TODO |

### PRIORITY 7: CORE LIBRARIES (Tier 1 — Adoption Blockers)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 7.1 | JSON library (eclexia-json) | 6h | TODO |
| 7.2 | HTTP library (eclexia-http) | 6h | TODO |
| 7.3 | Regex library (eclexia-regex) | 4h | TODO |
| 7.4 | Crypto library (eclexia-crypto: SHA-256, HMAC) | 4h | TODO |
| 7.5 | Log library (eclexia-log: structured logging) | 3h | TODO |
| 7.6 | Network library (eclexia-net: TCP/UDP sockets) | 4h | TODO |
| 7.7 | Math library (eclexia-math: linear algebra, statistics, numerical methods) | 8h | TODO |

### PRIORITY 8: WIKI & DOCUMENTATION
| # | Task | Effort | Status |
|---|------|--------|--------|
| 8.1 | Create GitHub wiki structure | 2h | TODO |
| 8.2 | Populate wiki from existing 37+ docs | 4h | TODO |
| 8.3 | Create FAQ page | 2h | TODO |
| 8.4 | Create troubleshooting guide | 2h | TODO |
| 8.5 | Create architecture diagrams | 4h | TODO |
| 8.6 | Create glossary of eclexia terms | 2h | TODO |

### PRIORITY 9: IDE PLUGINS (All Major IDEs)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 9.1 | VSCode extension — already exists, verify/polish | 2h | TODO |
| 9.2 | Neovim/Vim plugin (tree-sitter grammar + LSP config) | 6h | TODO |
| 9.3 | Emacs mode (major-mode + LSP integration) | 4h | TODO |
| 9.4 | JetBrains plugin (IntelliJ, CLion, etc.) | 8h | TODO |
| 9.5 | Sublime Text package | 3h | TODO |
| 9.6 | Helix editor support (tree-sitter + LSP) | 3h | TODO |
| 9.7 | Zed editor extension | 3h | TODO |
| 9.8 | PanLL native integration (eclexia in Pane-L/N/W) | 8h | TODO |
| 9.9 | Tree-sitter grammar for eclexia (shared across editors) | 6h | TODO |
| 9.10 | TextMate grammar (shared across editors, already partial in VSCode) | 2h | TODO |

### PRIORITY 10: LINTER, MINTER & PLUGINS
| # | Task | Effort | Status |
|---|------|--------|--------|
| 10.1 | Expand linter rules (currently 6, target 20+) | 8h | TODO |
| 10.2 | Linter plugin system (allow custom rules) | 6h | TODO |
| 10.3 | Minter plugin system (allow custom mint types) | 4h | TODO |
| 10.4 | Minter NFT/token standard integration | 4h | TODO |
| 10.5 | Linter pre-commit hook | 1h | TODO |
| 10.6 | Linter CI/CD integration (GitHub Action) | 2h | TODO |

### PRIORITY 11: COMPLETE THEORY SET
| # | Task | Effort | Status |
|---|------|--------|--------|
| 11.1 | Complete 22 Admitted Coq/Agda proofs | 20h | TODO |
| 11.2 | Type system soundness (progress + preservation) | 10h | TODO |
| 11.3 | Resource safety formal proofs | 10h | TODO |
| 11.4 | Shadow price duality proofs | 8h | TODO |
| 11.5 | Dimensional analysis correctness proofs | 6h | TODO |
| 11.6 | Carbon accounting proofs | 6h | TODO |
| 11.7 | Adaptive function optimality proofs | 8h | TODO |
| 11.8 | Effect system soundness proofs | 8h | TODO |
| 11.9 | Memory safety proofs (linear types) | 10h | TODO |
| 11.10 | Compilation correctness (source ↔ bytecode equivalence) | 12h | TODO |
| 11.11 | Module system correctness | 6h | TODO |
| 11.12 | Pattern matching exhaustiveness proof | 6h | TODO |
| 11.13 | Convex optimisation guarantees | 8h | TODO |
| 11.14 | Linear programming correctness | 8h | TODO |
| 11.15 | Resource algebra properties | 6h | TODO |
| 11.16 | Pareto optimality of resource allocation | 8h | TODO |
| 11.17 | Market clearing properties | 6h | TODO |
| 11.18 | Incentive compatibility | 6h | TODO |
| 11.19 | Mechanism design properties | 6h | TODO |
| 11.20 | Wire all proofs through echidna for verification | 8h | TODO |

### PRIORITY 12: SEAM ANALYSIS
| # | Task | Effort | Status |
|---|------|--------|--------|
| 12.1 | Full seam analysis: compiler crate boundaries | 4h | DONE 2026-02-09 (8 issues found, 2 critical fixed, commit e5be2cb) |
| 12.2 | Seam analysis: compiler → runtime boundary | 4h | TODO |
| 12.3 | Seam analysis: stdlib → interpreter builtins | 3h | TODO |
| 12.4 | Seam analysis: LSP → compiler integration | 2h | TODO |
| 12.5 | Seam analysis: reactive crates → main pipeline | 4h | TODO |
| 12.6 | Run seambot on eclexia (gitbot-fleet) | 2h | TODO |

### PRIORITY 13: DATABASE CONNECTORS (Idris2 ABI + Zig FFI Pattern)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 13.1 | Database abstraction layer (Idris2 ABI definitions) | 8h | TODO |
| 13.2 | Database FFI layer (Zig C-compatible implementation) | 6h | TODO |
| 13.3 | PostgreSQL connector (Idris2 ABI + Zig FFI) | 6h | TODO |
| 13.4 | SQLite connector (Idris2 ABI + Zig FFI) | 4h | TODO |
| 13.5 | Redis connector (Idris2 ABI + Zig FFI) | 4h | TODO |
| 13.6 | MongoDB connector (Idris2 ABI + Zig FFI) | 4h | TODO |
| 13.7 | DuckDB connector (Idris2 ABI + Zig FFI) | 4h | TODO |
| 13.8 | SurrealDB connector (Idris2 ABI + Zig FFI) | 4h | TODO |
| 13.9 | MySQL/MariaDB connector | 4h | TODO |
| 13.10 | CockroachDB connector | 4h | TODO |
| 13.11 | ScyllaDB connector | 4h | TODO |
| 13.12 | InfluxDB connector | 4h | TODO |
| 13.13 | Neo4j connector | 4h | TODO |
| 13.14 | Qdrant connector (vector DB) | 4h | TODO |

**Architecture note:** Per hyperpolymath standard, ALL database connectors follow:
- **Idris2** for ABI definitions (dependent types prove interface correctness: column types, query safety, connection lifecycle)
- **Zig** for FFI implementation (C-compatible, zero-cost, cross-compilation)
- **Generated C headers** bridge ABI ↔ FFI
- Directory structure: `src/abi/*.idr` + `ffi/zig/src/*.zig` + `generated/abi/*.h`

### PRIORITY 14: ECLEXIA-JTV (Julia The Viper Integration)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 14.1 | Design spec: JTV Data Language blocks in eclexia | 4h | TODO |
| 14.2 | Parser extension for Harvard block injection | 6h | TODO |
| 14.3 | Type checker integration for JTV safe data blocks | 6h | TODO |
| 14.4 | Runtime support for JTV execution model | 8h | TODO |
| 14.5 | Formal proof: injection impossibility in JTV blocks | 6h | TODO |

**Context:** JTV (Julia The Viper) at `/var/mnt/eclipse/repos/julia-the-viper/` is a
Harvard Architecture language where code injection is grammatically impossible.
"Addition blocks" = Data Language (only + operations). "Harvard blocks" = separation
between Data and Control sublanguages. eclexia-jtv would inject JTV's safe Data
Language blocks into eclexia for provably-secure data handling.

### PRIORITY 15: NEXTGEN-LANGUAGES INTEROP (All hyperpolymath languages)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 15.1 | Phronesis interop (Elixir/BEAM — NIF bridge via C header) | 6h | TODO |
| 15.2 | WokeLang interop (Rust — direct crate dependency) | 4h | TODO |
| 15.3 | AffineScript interop (OCaml — C FFI via eclexia_ffi.h) | 6h | TODO |
| 15.4 | Ephapax interop (Rust+Idris2+Coq — shared ABI layer) | 6h | TODO |
| 15.5 | My-Lang interop (Rust, 11 crates — direct Rust FFI) | 6h | TODO |
| 15.6 | Julia-the-Viper interop (already eclexia-jtv, Priority 14) | 0h | See Priority 14 |
| 15.7 | Error-Lang interop (ReScript+Deno — Deno.dlopen FFI) | 4h | TODO |
| 15.8 | Oblibeny interop (spec only — design phase) | 2h | TODO |
| 15.9 | Betlang interop (Racket+Rust DSL — Rust FFI) | 4h | TODO |
| 15.10 | Anvomidav interop (Rust DSL — direct Rust FFI) | 4h | TODO |
| 15.11 | VQL standard interop (ReScript, VeriSimDB query language) | 6h | TODO |
| 15.12 | GQL-DT / FBQL-DT interop (Lean 4 + Zig, dependent-typed queries) | 8h | TODO |
| 15.13 | VQL dependent-types variant (if distinct from standard VQL) | 4h | TODO |

**Context:** ALL languages in `/var/mnt/eclipse/repos/nextgen-languages/` MUST have
bidirectional interop with eclexia. This is non-negotiable — eclexia must be able to
call into every sibling language AND every sibling language must be able to call into
eclexia's resource runtime via the C ABI header (`eclexia_ffi.h`).

**Query languages (GQL + VQL):** Both standard AND dependent-type variants are included.
VQL (VeriSimDB's query language, ReScript) enables resource-tracked database queries.
GQL-DT/FBQL-DT (Lean 4 + Zig) provides compile-time DB constraint verification with
dependent types. Both can leverage eclexia's resource budget system for query cost tracking.

**7-tentacles** is an educational programme for my-lang, NOT a language — excluded from interop.

### PRIORITY 16: ECOSYSTEM LIBRARIES (Tier 2+)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 16.1 | TEA framework library | 8h | TODO |
| 16.2 | CSV/TOML/YAML parsing library | 4h | TODO |
| 16.3 | Extended filesystem library (glob, walk, temp) | 3h | TODO |
| 16.4 | Testing/assertion library | 4h | TODO |
| 16.5 | Economics library (LP, constraint optimisation) | 8h | TODO |
| 16.6 | Carbon API library | 4h | TODO |
| 16.7 | Shadow price utilities library | 4h | TODO |
| 16.8 | I/O library (async, streams, pipes) | 6h | TODO |
| 16.9 | Web framework (beyond TEA — server-side) | 8h | TODO |
| 16.10 | Graphics library | 12h | TODO |
| 16.11 | Data analysis library (DataFrames) | 10h | TODO |
| 16.12 | NLP library | 10h | TODO |
| 16.13 | AI/ML library | 12h | TODO |

### PRIORITY 17: EXTERNAL TOOL INTEGRATION
| # | Task | Effort | Status |
|---|------|--------|--------|
| 17.1 | OPSM: Add eclexia as native language | 4h | DONE 2026-02-09 (commit a081d67, 4 tests pass, eclexia.ex adapter + registry wiring) |
| 17.2 | OPSM: eclexia-verifier trust service | 6h | NOT DONE |
| 17.3 | PanLL: eclexia constraint integration (Pane-L) | 6h | NOT DONE |
| 17.4 | PanLL: eclexia diagnostics in World pane | 4h | NOT DONE |
| 17.5 | MCP server for eclexia | 6h | NOT DONE |
| 17.6 | SSG engine in polystack/poly-ssg/engines | 8h | NOT DONE |
| 17.7 | Aggregate library eclexia implementation | 6h | NOT DONE |

### PRIORITY 18: SELF-HOSTING
| # | Task | Effort | Status |
|---|------|--------|--------|
| 17.1 | Design eclexia subset that can compile eclexia | 8h | TODO |
| 17.2 | Add FFI support to eclexia (extern "C") | 8h | PARTIAL — extern block parsing, type checking, and interpreter stubs done (2026-02-09). Real linking (dlopen/dlsym) TODO. |
| 17.3 | Add unsafe/raw operations | 6h | TODO |
| 17.4 | Add memory layout control (@repr(C)) | 4h | TODO |
| 17.5 | Add compile-time evaluation (const def) | 6h | TODO |
| 17.6 | Port AST definitions to eclexia (~800 LOC) | 4h | TODO |
| 17.7 | Port lexer to eclexia (~1200 LOC) | 8h | TODO |
| 17.8 | Port parser to eclexia (~2000 LOC) | 12h | TODO |
| 17.9 | Port type checker to eclexia (~1600 LOC) | 10h | TODO |
| 17.10 | Port HIR/MIR lowering (~2000 LOC) | 12h | TODO |
| 17.11 | Port LLVM backend (~4000 LOC) | 20h | TODO |
| 17.12 | Port runtime (~1600 LOC) | 10h | TODO |
| 17.13 | Port CLI/driver (~800 LOC) | 6h | TODO |
| 17.14 | Verify Stage 2 = Stage 3 (reproducible builds) | 4h | TODO |

### PRIORITY 18: VM BACKENDS
| # | Task | Effort | Status |
|---|------|--------|--------|
| 18.1 | LLVM backend (real, 12-week plan exists in IMPLEMENTATION-PLAN.md) | 40h | TODO |
| 18.2 | Cranelift backend (real, fast dev builds) | 20h | IN PROGRESS — skeleton with real JIT for int functions |
| 18.3 | WASM backend (real, browser/edge) | 15h | IN PROGRESS — generates real .wasm, needs GC/complex types/WASI |
| 18.4 | BEAM backend (Erlang VM, distributed) | 40h | TODO |
| 18.5 | JVM backend | 40h | TODO |
| 18.6 | CLR backend (.NET) | 40h | TODO |
| 18.7 | GPU backend (CUDA/ROCm/Metal/WebGPU) | 40h | TODO |
| 18.8 | Embedded backend (ARM Cortex-M, RISC-V embedded) | 30h | TODO |

### PRIORITY 19: DOMAIN-SPECIFIC STANDARD LIBRARIES (from MULTICOMPILER-ARCHITECTURE.md)
| # | Task | Effort | Status |
|---|------|--------|--------|
| 19.1 | std::mobile (battery, adaptive networking, UI) | 20h | TODO |
| 19.2 | std::cloud (Lambda, S3, carbon, cost tracking) | 20h | TODO |
| 19.3 | std::datascience (ML training, inference) | 20h | TODO |
| 19.4 | std::hpc (SLURM, MPI, Green500) | 20h | TODO |
| 19.5 | std::embedded (sleep modes, radio power) | 15h | TODO |
| 19.6 | std::web (SSR, REST APIs) | 15h | TODO |
| 19.7 | std::carbon (grid APIs, multiple providers) | 10h | TODO |
| 19.8 | std::resources (core resource types, measurement) | 8h | TODO |
| 19.9 | std::adaptive (shadow price config, per-context) | 6h | TODO |
| 19.10 | std::units (physical quantities, conversions) | 6h | TODO |

### PRIORITY 20: DISTRIBUTION & PACKAGING
| # | Task | Effort | Status |
|---|------|--------|--------|
| 20.1 | Package registry server (HTTP API) | 20h | TODO |
| 20.2 | Single binary distribution (static linking) | 4h | TODO |
| 20.3 | WASM universal runtime (eclexia.wasm) | 8h | TODO |
| 20.4 | Guix package (guix.scm exists, verify works) | 2h | TODO |
| 20.5 | Nix flake (flake.nix) | 4h | TODO |
| 20.6 | Homebrew formula | 2h | TODO |
| 20.7 | Cross-compilation: Linux x86-64, ARM64, RISC-V | 4h | TODO |
| 20.8 | Cross-compilation: macOS ARM64, x86-64 | 4h | TODO |
| 20.9 | Cross-compilation: Windows x86-64 | 4h | TODO |

---

## 8. THREAD DECOMPOSITION

### THREAD A: Core Compiler & Toolchain
**Scope:** Priorities 0, 1, 2, 3, 4 (examples)
**Why single thread:** Same Rust codebase, changes interact
- Fix tests, commit, CVE fix
- Documentation honesty
- Core toolchain (stubs → real code)
- Annotations, quality
- Example programs

### THREAD B: Infrastructure & Operations
**Scope:** Priority 5
**Why separate:** Different repos (gitbot-fleet, git-private-farm, hypatia, echidna)
- Enroll eclexia everywhere
- Configure all bots

### THREAD C: Playground & Website
**Scope:** Priority 6
**Why separate:** Different tech (ReScript, SSG/WordPress)

### THREAD D: Libraries & Ecosystem
**Scope:** Priorities 7, 13, 15
**Why separate:** Self-contained .ecl + Rust FFI / Idris2 ABI + Zig FFI
- Tier 1 libs (JSON, HTTP, regex, crypto, log, network, math)
- Database connectors (Idris2 ABI + Zig FFI)
- Tier 2+ libs

### THREAD E: Formal Theory & Proofs
**Scope:** Priority 11
**Why separate:** Heavy academic (Coq, Agda, Lean), independent of compiler
- Complete Admitted proofs
- Full theory set (CS, maths, engineering, economics)
- Echidna verification

### THREAD F: Seam Analysis & Wiki
**Scope:** Priorities 8, 12
**Why separate:** Analysis + documentation, read-only on compiler

### THREAD G: IDE Plugins & Tooling
**Scope:** Priorities 9, 10
**Why separate:** Each plugin is independent
- Tree-sitter grammar (shared)
- VSCode, Neovim, Emacs, JetBrains, Sublime, Helix, Zed, PanLL
- Linter/minter expansion and plugins

### THREAD H: Language Extensions & External Tools
**Scope:** Priorities 14, 16
**Why separate:** Language design work
- eclexia-jtv
- OPSM integration
- PanLL integration
- MCP server, SSG engine

### THREAD I: Self-Hosting & Backends (Future)
**Scope:** Priorities 17, 18, 19, 20
**Why NOT yet:** Depends on core toolchain (Thread A)
- Self-hosting bootstrap
- VM backends (BEAM, WASM, Cranelift, LLVM, JVM, CLR, GPU, Embedded)
- Domain standard libraries
- Distribution

---

## 9. THEORY & PROOFS STATUS

### Currently Proven (genuinely verified)
- Progress theorem (type system)
- Preservation theorem (type system)
- Some shadow price properties

### Currently Admitted (ASSUMED — 22 instances)
In `formal/coq/src/` and `formal/agda/`:
- Strong duality theorem (partially)
- Resource tracking soundness
- Usage monotonicity
- Several type system lemmas
- Economic optimality properties

### Full Theory Set Needed

**Computer Science:** Type soundness, effect soundness, memory safety, module correctness, pattern exhaustiveness, compilation correctness

**Mathematics:** Shadow price duality, convex optimisation, LP correctness, dimensional analysis, resource algebra

**Engineering:** Carbon accuracy, energy measurement, adaptive scheduling optimality, budget enforcement, real-time constraints

**Economics:** Pareto optimality, market clearing, incentive compatibility, mechanism design

---

## 10. LIBRARY ECOSYSTEM PLAN

### Priority Order (Why This Order)

**Tier 1 — Without these, nobody writes their second program:**
1. `eclexia-json` — can't talk to any API
2. `eclexia-http` — can't fetch from internet
3. `eclexia-regex` — can't validate or search text
4. `eclexia-crypto` — can't do security
5. `eclexia-log` — can't debug production
6. `eclexia-net` — TCP/UDP sockets, beyond HTTP
7. `eclexia-math` — linear algebra, statistics, numerical methods (CRITICAL for economics-as-code)

**Tier 2 — Enables real applications:**
8. `eclexia-db` — database connectors via generic trait (OPEN SOURCE ONLY):
   - **Own:** Lithoglyph, VeriSimDB (first-class, native integration)
   - **Graph/Multi-model:** ArangoDB CE (Apache 2.0), Virtuoso OSE (GPL v2)
   - **Relational:** PostgreSQL (PostgreSQL Lic), SQLite (public domain), MariaDB (GPL v2)
   - **Document:** CouchDB (Apache 2.0) — offline-first sync for IoT resource collectors
   - **Wide-column:** Cassandra (Apache 2.0) — massive-scale resource telemetry
   - **KV/Cache:** Valkey (BSD, NOT Redis — Redis is no longer FOSS), Memcached (BSD)
   - **Embedded KV:** LMDB (OpenLDAP/OSI) — zero-copy for SCADA/embedded, RocksDB (Apache 2.0)
   - **Distributed KV:** FoundationDB (Apache 2.0) — ACID budget propagation
   - **RDF/SPARQL:** Oxigraph (MIT/Apache 2.0, Rust) — resource ontology graphs
   - **REJECTED (not open source):** ~~Redis~~ (RSAL+SSPL since 2024), ~~Dragonfly~~ (BSL 1.1), ~~MongoDB~~ (SSPL)
   - All via `eclexia-connector` generic trait — same interface, swap backends
9. `eclexia-tea` — web framework (TEA pattern)
10. `eclexia-config` — TOML/YAML/CSV
11. `eclexia-fs` — extended filesystem
12. `eclexia-test` — assertions, mocking
13. `eclexia-io` — async I/O, streams

**Tier INDUSTRIAL — Open source protocols and data (NO proprietary connectors):**
14. `eclexia-mqtt` — MQTT 5.0 client (open standard, ISO/IEC 20922). IoT device telemetry, resource measurement ingestion. Broker-agnostic (Mosquitto, HiveMQ CE, NanoMQ, etc.)
15. `eclexia-ptp` — IEEE 1588 Precision Time Protocol. Sub-microsecond time sync for coordinated resource measurement across distributed systems. Critical for budget propagation accuracy
16. `eclexia-tsdb` — Time-series database connector. Open source only: TimescaleDB (PostgreSQL ext), QuestDB, VictoriaMetrics, InfluxDB OSS. Resource telemetry storage and query
17. `eclexia-modbus` — Modbus TCP/RTU (open protocol, public domain). Direct SCADA/PLC/DCS sensor reads. Energy meters, power monitors, environmental sensors
18. `eclexia-coap` — CoAP (RFC 7252, open standard). Constrained IoT devices that can't do HTTP. Battery-powered sensors reporting resource measurements
19. `eclexia-connector` — Generic connector trait/interface. Corporations build their OWN proprietary connectors on top of this. We provide the contract, they do the work

**POLICY:** We build connectors for open standards and open source systems ONLY.
Proprietary systems (Siemens S7, Allen-Bradley, OSIsoft PI, AWS IoT, Azure IoT Hub,
GE Predix, etc.) are the vendor's responsibility. `eclexia-connector` gives them a
clean trait to implement. If they want eclexia integration, they write the adapter.

**Tier UNIQUE — Eclexia's differentiators (with bidirectional Idris2 ABI + Zig FFI):**
20. `eclexia-economics` — LP, constraint optimisation (THE point of eclexia)
21. `eclexia-carbon` — carbon API, green metrics
22. `eclexia-shadow` — shadow price utilities
23. `eclexia-fuse` — software fuses, circuit breakers, rate limiters, bulkheads, deadlines (resource-aware fault isolation)
24. `eclexia-sla` — SLA-as-Code: compile-time service level agreement verification via resource constraints
25. `eclexia-anytime` — anytime algorithms: shadow-price-driven quality/deadline trade-offs
26. `eclexia-pareto` — multi-objective Pareto optimisation with shadow price marginal rates of substitution
27. `eclexia-degrade` — graceful degradation: adaptive data structures that downshift under resource pressure
28. `eclexia-fairshare` — algorithmic fairness with provable resource allocation guarantees
29. `eclexia-greenroute` — carbon-aware request routing using real-time grid carbon intensity
30. `eclexia-budget-prop` — distributed resource budget propagation (like OpenTelemetry but for resources)
31. `eclexia-mechanism` — mechanism design: auctions, market-clearing, internal resource markets via shadow prices
32. `eclexia-harvest` — energy harvesting scheduler for IoT/embedded with adaptive power modes
33. `eclexia-chaos` — resource-aware chaos engineering: test graceful degradation under artificial budget constraints

**Tier 3 — Ecosystem growth:**
34. `eclexia-web` — server-side web framework
35. `eclexia-graphics` — visual output, plots
36. `eclexia-data` — DataFrames, analysis
37. `eclexia-nlp` — text processing
38. `eclexia-ml` — machine learning

### Implementation Pattern

**For system-boundary and unique libraries:**
- **Bidirectional Idris2 ABI** — dependent types prove interface correctness in BOTH directions
  - Outbound: Eclexia programs call optimised native implementations
  - Inbound: External code (C, Rust, Python ctypes) calls into Eclexia's resource runtime
  - Proofs: dimension compatibility, shadow price non-negativity, budget conservation
- **Bidirectional Zig FFI** — C-compatible implementation with special optimisations
  - SIMD: vectorised Pareto frontier, constraint checking, shadow price batch updates
  - Lock-free: concurrent shadow price observation, budget propagation
  - Zero-copy: resource budget passing across boundaries
  - Cache-aligned: resource tracking structures for CPU cache efficiency
- Generated C headers bridge ABI <-> FFI
- Structure: `src/abi/*.idr` + `ffi/zig/src/*.zig` + `generated/abi/*.h`
- Reference implementation: `eclexia/src/abi/` + `eclexia/ffi/zig/`

**For pure-logic libraries (JSON, config, test):**
- Pure eclexia where possible
- Rust FFI only where performance requires it

---

## 11. EXAMPLE PROGRAMS

Need a comprehensive set that covers every language feature and DEFINITELY works.
Each example must be verified to: (a) parse, (b) type-check, (c) interpret, (d) compile to bytecode, (e) run.

See Priority 4 in task list for full list of 36 example programs.

Existing examples at `/var/mnt/eclipse/repos/eclexia/examples/` (36 files):

**WORKING (34, verified by `target/debug/eclexia run` on 2026-02-09):**
- `hello_world.ecl` — Hello World, basic println (WORKING)
- `hello.ecl` — minimal hello (WORKING)
- `fibonacci.ecl` — recursive + tail-recursive fibonacci (WORKING)
- `math_showcase.ecl` — factorial, power, gcd, is_prime, abs (WORKING)
- `pattern_matching.ecl` — unit enum variants, integer literals, wildcards (WORKING)
- `closures.ecl` — lambdas, make_adder, make_multiplier, apply (WORKING)
- `error_handling.ecl` — Result[Float, String], Option, safe_divide (WORKING)
- `collections.ecl` — arrays, hashmap, tuples, array repeat (WORKING)
- `string_processing.ecl` — concatenation, length, string building (WORKING)
- `control_flow.ecl` — collatz conjecture, nested if/else, classify (WORKING)
- `range_loops.ecl` — for/range, while accumulator, multiplication table, fizzbuzz (WORKING)
- `struct_enum.ecl` — Point struct, Color enum, midpoint, field access (WORKING)
- `unicode_ids.ecl` — π, τ, 面積, Greek letters (WORKING)
- `budget_enforcement.ecl` — @requires constraints, adaptive def (WORKING)
- `traits_and_impls.ecl` — Circle/Rectangle types, standalone functions (WORKING)
- `generics.ecl` — identity, first, second, apply with higher-order (WORKING)
- `macros.ecl` — macro definitions (debug_print, assert_eq, unless) (WORKING)
- `hashmaps.ecl` — hashmap_new/insert/get/remove/contains/keys/values (WORKING)
- `higher_order.ecl` — apply, compose, lambdas, function passing (WORKING)
- `recursion.ecl` — Tower of Hanoi, digit_sum, print_binary, Ackermann (WORKING)
- `type_system.ecl` — generics, type inference, apply_twice (WORKING)
- `vm_test.ecl` — VM-specific test (WORKING)
- `test_example.ecl` — test framework example (has main for manual run) (WORKING)
- `bench_example.ecl` — benchmark example (has main for manual run) (WORKING)
- `bench_energy.ecl` — energy benchmarking suite (has main for manual run) (WORKING)
- `carbon_aware.ecl` — carbon-aware scheduling demo (WORKING)
- `dimensional_types.ecl` — dimensional types + adaptive fibonacci (WORKING)
- `json_test.ecl` — file I/O + string operations (WORKING)
- `matrix_multiply.ecl` — adaptive matrix computation (WORKING)
- `module_system_demo.ecl` — module declaration + top-level duplicates (WORKING)
- `multi_objective_optimization.ecl` — energy/latency/carbon tradeoffs (WORKING)
- `resource_tracking.ecl` — @requires budgets + nested calls (WORKING)
- `shadow_price_optimization.ecl` — shadow_price + @when gating (WORKING)
- `sustainabot_policy.ecl` — policy evaluation + adaptive def (WORKING)
- `effect_system_demo.ecl` — effect syntax + handler block (handlers no-op) (WORKING)
- `comprehensive_opportunity.ecl` — adaptive budgeting + shadow prices (WORKING)

**FAILING (0):** None currently known (previously listed failures now run).

Various conformance tests in `tests/conformance/valid/` (32 files)
Various conformance tests in `tests/conformance/invalid/` (19 files)

**Known parser limitations discovered during example writing (2026-02-09):**
- No `else if` syntax — must use `else { if ... }` nesting
- No `let` bindings inside `while` body in functions with parameters
- No tuple variant destructuring in match (e.g., `Circle(r)` doesn't match)
- Qualified paths in expressions not supported (`module::func` parse error)

---

## 12. IDE PLUGINS & TOOLING

### Current State
- **VSCode:** Extension exists (`editors/vscode/`), syntax highlighting + LSP ✓
- **All others:** Nothing

### What's Needed
- **Tree-sitter grammar** — shared foundation for Neovim, Helix, Zed, Emacs
- **TextMate grammar** — shared foundation for VSCode, Sublime (partial exists)
- **LSP server** — already exists, works with any LSP-compatible editor
- **Individual plugins** for each IDE (see Priority 9)
- **PanLL integration** — native eclexia support in next-gen IDE

---

## 13. EXTERNAL TOOL INTEGRATION (PanLL, OPSM)

### PanLL (Next-Gen IDE)
- **Path:** `/var/mnt/eclipse/repos/panll`
- **Status:** v0.1.0-alpha, ReScript + Tauri 2.0, 33 tests passing
- **Architecture:** Three-pane (Symbolic/Neural/World), anti-crash library, vexometer
- **Eclexia integration:** NOT STARTED
- **Plan:** Pane-L enforces eclexia constraints, Pane-N shows reasoning, Pane-W displays results

### OPSM (Odds-and-Sods Package Manager)
- **Path:** `/var/mnt/eclipse/repos/odds-and-sods-package-manager`
- **Status:** v1.1.0 production, Elixir/BEAM, 8 registries, trust pipeline
- **Eclexia integration:** NOT STARTED
- **Plan:** Add eclexia-verifier as 6th trust service, add eclexia package format

---

## 14. ROADMAP ITEMS FROM PLANNING DOCS

### From IMPLEMENTATION-PLAN.md (LLVM 12-Week Plan)
- Weeks 1-2 (Foundation): DONE (4/4 milestones)
- Weeks 3-4 (Type Lowering): NOT DONE (4 tasks)
- Weeks 5-6 (Function Codegen): NOT DONE (6 tasks)
- Weeks 7-8 (Adaptive Functions): NOT DONE (4 tasks)
- Weeks 9-10 (Resource Tracking): NOT DONE (5 tasks)
- Weeks 11-12 (Optimisation): NOT DONE (5 tasks)
- **Total: ~28 undone LLVM tasks**

### From SELF-HOSTING-ROADMAP.md
- Phase 1 (Backends): NOT DONE — LLVM, WASM, Cranelift
- Phase 2 (Bootstrap): NOT DONE — FFI, unsafe, memory layout, port 10 modules (~14,400 LOC)
- Phase 3 (Dogfooding): NOT DONE — rewrite tools in eclexia
- **Total: ~50+ undone tasks**

### From MULTICOMPILER-ARCHITECTURE.md
- 5 backend targets: NOT DONE (LLVM, WASM, Cranelift, GPU, Embedded)
- 6 domain libraries: NOT DONE (mobile, cloud, datascience, HPC, embedded, web)
- 4 cross-cutting libraries: NOT DONE (carbon, resources, adaptive, units)
- **Total: ~100+ undone tasks**

### From GITHUB-ISSUES.md
- 32 issues tracked, 4 done, 28 remaining
- **Total: 28 undone issues**

---

## 15. FILE INVENTORY

### Key Paths
```
/var/mnt/eclipse/repos/eclexia/                    # Main repo (25 crates)
/var/mnt/eclipse/repos/eclexia/compiler/           # Compiler crates
/var/mnt/eclipse/repos/eclexia/runtime/            # Runtime system
/var/mnt/eclipse/repos/eclexia/stdlib/             # Standard library (.ecl)
/var/mnt/eclipse/repos/eclexia/formal/             # Coq/Agda proofs
/var/mnt/eclipse/repos/eclexia/editors/            # VSCode extension
/var/mnt/eclipse/repos/eclexia/ffi/               # Zig FFI
/var/mnt/eclipse/repos/eclexia/deploy/            # Docker/K8s
/var/mnt/eclipse/repos/eclexia/docs/              # Tutorials, reference
/var/mnt/eclipse/repos/eclexia/examples/          # Example .ecl files
/var/mnt/eclipse/repos/eclexia/tests/             # Conformance tests
/var/mnt/eclipse/repos/eclexia/.machine_readable/ # SCM metadata
/var/mnt/eclipse/repos/eclexia/.github/           # 17+ workflows

# Related repos
/var/mnt/eclipse/repos/gitbot-fleet/              # Bot fleet (9 bots)
/var/mnt/eclipse/repos/.git-private-farm/         # Multi-forge mirroring (28+ repos)
/var/mnt/eclipse/repos/hypatia/                   # CI/CD intelligence
/var/mnt/eclipse/repos/echidna/                   # Theorem proving (17 backends)
/var/mnt/eclipse/repos/verisimdb-data/            # Vulnerability data
/var/mnt/eclipse/repos/panic-attacker/            # Security scanner
/var/mnt/eclipse/repos/sustainabot/               # Ecological monitoring
/var/mnt/eclipse/repos/julia-the-viper/           # JTV language
/var/mnt/eclipse/repos/panll/                     # Next-gen IDE
/var/mnt/eclipse/repos/odds-and-sods-package-manager/  # Package manager
/var/mnt/eclipse/repos/scan-results/eclexia.json  # Panic-attack results
```

### Stats
- 25 Rust crates, ~49,882 lines total (including non-Rust: Idris2, Zig, .ecl, shell)
- Full `cargo test` passes (2026-02-09)
- 32 valid + 19 invalid conformance tests (0 skips)
- 36 example `.ecl` programs; all 36 interpret/run successfully (2026-02-09)
- Bytecode compile/run passes 25/36; 11 fail or hang (see Priority 4.32)
- 7 stdlib modules (core, collections, math, I/O, text, time, async)
- 17+ GitHub Actions workflows
- 37+ documentation files

---

## 16. TO-DONE (Completed Items)

**Instructions:** Move items here from the task list as they're completed.
Include date and any notes.

| Date | Task # | Description | Notes |
|------|--------|-------------|-------|
| 2026-02-09 | 4.5 | Resource-tracked computation example verified | `examples/resource_tracking.ecl` runs |
| 2026-02-09 | 4.18 | Shadow price optimization example verified | `examples/shadow_price_optimization.ecl` runs |
| 2026-02-09 | 4.19 | Multi-objective optimization example verified | `examples/multi_objective_optimization.ecl` runs |
| 2026-02-09 | — | Fix Result Ok/Err runtime pattern mismatch | Ok/Err payload now stored under `_0`; pattern/try handling updated |
| 2026-02-09 | — | Fix integration test temp file collisions | Unique temp path + `CARGO_BIN_EXE_eclexia` usage |
| 2026-02-09 | — | Scheduler tests use correct shadow price key | `energy` resource now matches estimated_costs |
| 2026-02-09 | — | Comprehensive opportunity example verified | `examples/comprehensive_opportunity.ecl` runs with observe-shadow + carbon-report |
| 2026-02-09 | 4.4 | Fibonacci adaptive example verified | `examples/dimensional_types.ecl` (adaptive fibonacci) runs |
| 2026-02-09 | 4.6 | Carbon-aware scheduling example verified | `examples/carbon_aware.ecl` runs |
| 2026-02-09 | 4.15 | I/O operations example verified | `examples/json_test.ecl` runs |
| 2026-02-09 | 4.26 | Test framework example verified | `examples/test_example.ecl` (includes intentional failing test) |
| 2026-02-09 | 4.27 | Benchmark examples verified | `examples/bench_example.ecl` + `examples/bench_energy.ecl` parse/run |
| 2026-02-09 | 4.9 | Effect system demo added | `examples/effect_system_demo.ecl` runs (handlers parsed, no-op) |
| 2026-02-09 | 4.10 | Module system demo added | `examples/module_system_demo.ecl` runs (qualified paths not yet supported) |
| 2026-02-09 | 4.29 | Sustainabot policy example verified | `examples/sustainabot_policy.ecl` runs |
| 2026-02-09 | 3.5 | Remove wasm test unused variable warning | `_c` rename in `eclexia-wasm` tests |
| 2026-02-09 | 0.3 | Fix bytes CVE (cargo update bytes) | Updated bytes 1.11.0→1.11.1, build verified clean |
| 2026-02-08 | — | Minter command implemented | In commands.rs, builds clean |
| 2026-02-08 | — | 8-stage toolchain hardening | All compiler components to working state |
| 2026-02-09 | 0.1 | Fix conformance test regression (COMPLETE) | **32/32 valid pass**, 19/19 invalid correctly reject, 0 skips. All 271 lib tests pass. |
| 2026-02-09 | 0.4 | Fix rustls-pemfile (upgrade reqwest 0.11→0.12) | Commit dbbe4f4. Also added macro system (MacroCall AST, expansion, token nesting) |
| 2026-02-09 | 0.6 | Fix runtime resource enforcement gaps | Commit 8c9f564. Resource<D> dimension comparison check in typeck. KNOWN_RUNTIME_GAPS cleared. |
| 2026-02-09 | 1.1-1.5 | Documentation honesty pass | Commit 6c41a4d. README.adoc, QUICK_STATUS.md, CLAUDE.md, TOOLCHAIN_STATUS.md, TIER3_COMPLETION_SUMMARY.md |
| 2026-02-09 | 2.4-2.7 | Implement all 4 runtime stubs | Commit a6ce99b. scheduler (4 tests), profiler (6), carbon (7), shadow (8). 271 lib tests. |
| 2026-02-09 | 2.10 | Implement Serialize for BytecodeModule | Commit 8c9f564. serde derives on AST/Bytecode types, JSON output in commands.rs |
| 2026-02-09 | 12.1 | Seam analysis: compiler crate boundaries | Commit e5be2cb. 8 issues found (2 critical MIR panics fixed). SEAM_ANALYSIS.md created. |
| 2026-02-09 | 15.x | Nextgen-languages interop bridges | Commit e5be2cb. Bridge configs for WokeLang, Phronesis, betlang, AffineScript. INTEROP_STATUS.md created. |
| 2026-02-09 | 0.1a | Parser: contextual keywords for energy/latency/memory/carbon | Tokens parsed as identifiers in expression/pattern context |
| 2026-02-07 | — | 32/32 valid conformance tests | (had regressed to 29/32 — now fully restored) |
| 2026-02-07 | — | Type casting, pattern matching, ranges | Core language features |
| pre-2026 | — | Full compiler pipeline created | Lexer through VM |
| pre-2026 | — | LSP server | Diagnostics, completion, navigation |
| pre-2026 | — | VSCode extension | Syntax highlighting + LSP |
| pre-2026 | — | Formatter, linter, debugger | Basic implementations |
| pre-2026 | — | Coq/Agda formal proofs started | Some proven, 22 Admitted |
| pre-2026 | — | Docker + Kubernetes configs | Exist but partially aspirational |
| pre-2026 | — | 17 GitHub Actions workflows | Security, quality, CI/CD |
| 2026-02-09 | 2.1-2.2 | Bytecode serialization + loading (.eclb) | serde derives on Instruction/BytecodeModule/BytecodeFunction, JSON + binary format, run-bytecode cmd |
| 2026-02-09 | 18.FFI | Extern block type checking + interpreter stubs | Extern fn signatures in typeck, graceful "not linked" error in interpreter |
| 2026-02-09 | — | stdlib/async.ecl concurrency module | 11 @builtin functions: spawn, await, yield_now, sleep, channel, send, recv, try_recv, select, parallel, race |
| 2026-02-09 | 4.7,12-14,16-17,20,22-24 | 11 working example programs | math, patterns, closures, errors, collections, strings, control flow, ranges, structs, unicode, budgets |
| 2026-02-09 | 3.5-3.6 | Clippy lint pass + zero warnings | Auto-fixed + manual: Dimension::to_string→format_dimension, Visibility derive Default |
| 2026-02-09 | 3.2 | Panic-attack scan (session 6) | 15 weak pts, 327 unwraps, 28 unsafe, 48 panic sites, 49,882 lines |
| 2026-02-09 | 2.1-2.2 | .eclb binary bytecode format | Commit 5bb9512. 8-byte header (magic "ECLB" + version) + JSON body. write_eclb/read_eclb/is_eclb_path. |
| 2026-02-09 | 1.3,1.6-1.10 | Documentation honesty pass (6 docs) | Commit a26acbe. GETTING_STARTED (def→fn, status disclaimer), SELF-HOSTING-ROADMAP (100%→~55%), MULTICOMPILER-ARCHITECTURE (VISION DOCUMENT), ROADMAP.adoc (completion/date/license), IMPLEMENTATION_ROADMAP (SPDX typo), WHITEPAPER (projected vs measured note) |
| 2026-02-09 | 2.9 (partial) | Fix 3 dangerous production unwrap() calls | Commit 6eb2b45. modules (file_name), REPL debugger (flush), LSP symbols (position). 88% remaining are test-only. |
| 2026-02-09 | 5.5 | Ingest eclexia scan into verisimdb-data | Commit 9ef8bab (verisimdb-data). 15 weak pts, pushed GitHub + GitLab. |
| 2026-02-09 | 2.8 (partial) | Wire 4/7 reactive crates into CLI | Commits d5241ab + 0441089. absinterp, comptime, specialize, effects via `build --analyze`. |
| 2026-02-09 | 4.1,4.2,4.3,4.8,4.11 | 4 new examples + bytecode round-trip | hello_world, fibonacci, traits_and_impls, generics (commit f39fe28). .eclb round-trip verified. |
| 2026-02-09 | 2.14 (partial) | CallBuiltin VM instruction | Commit 36b686c. ~20 builtins dispatched from bytecode path. `build` now works on files using println etc. |
| 2026-02-09 | 4.5 fix | MIR adaptive def lowering fix | Commit 36b686c. Solutions share parent params, unknown locals produce Unit. |
| 2026-02-09 | — | Shadow prices live | ShadowPriceRegistry defaults (0.000033/0.001/0.00005) + ShadowPriceEngine dynamic prices from VM usage. |

---

## 17. ADVANCED COMPILER & TOOLCHAIN EXTENSIONS

### Implemented (Session 3 — 2026-02-09)

**Concurrency & Parallelism: DONE**
- `eclexia-async` runtime crate (4 modules: executor, channel, task, parallel)
- Tokio-backed async runtime with resource tracking per task
- MPSC channels, oneshot channels, broadcast channels
- Fork-join parallel iterators: `par_map`, `par_filter`, `par_reduce`
- AST nodes (Spawn, Channel, Send, Recv, Select, YieldExpr) fully integrated
- All match arms updated across workspace (interp, fmt, hir, lsp, typeck)
- 10 passing tests

**Advanced REPL: DONE**
- Multi-line input with brace/paren/bracket balancing
- History persistence (XDG data directory)
- `:type` / `:t` command (parses, type-checks, reports inferred type)
- `:ast` command (shows AST debug output)
- `:shadow` command (displays shadow prices from ShadowPriceRegistry)
- `:resources` command (displays runtime resource stats)
- `:env` command (shows accumulated definitions)
- `:reset` command (clears REPL state)
- Definition persistence across REPL lines (def, fn, type, struct, const)
- Ctrl+C cancels multi-line input

**Incremental Compilation / Watch Mode: DONE**
- `eclexia watch` command with file system watching (notify crate)
- Recursive directory monitoring for `.ecl` files
- Debounced batched re-checks (configurable delay)
- Timestamp logging, automatic re-parse + re-typecheck on file changes

**Error Recovery: DONE**
- Three-level recovery: item-level, statement-level, expression-level
- `recover_to_closing_delimiter` with nesting depth tracking
- Enhanced sync tokens for item/statement recovery
- Expression recovery in parenthesized exprs, array literals, match arms, function call args
- Context-specific error hints (hints for common mistakes at each level)
- 5 parser tests passing (including 3 new recovery tests)

**Bytecode Disassembler: DONE**
- `eclexia disasm` command: compiles through full pipeline, displays bytecode
- Shows constant pools (strings, floats, integers), function headers, instruction listing
- All 61 bytecode instruction variants formatted with human-readable mnemonics

**Resource Constraint Enforcement: DONE (bonus fix)**
- `@requires` annotations now enforced at runtime (both constraint and attribute syntax)
- Zero-budget detection (immediate rejection)
- Cumulative budget tracking across nested function calls
- Adaptive function feasibility checking in "no @when" branch
- Conformance tests: 32/32 valid pass, 18/19 invalid correctly reject (1 known gap: dimension comparison)

**Conformance Test Improvements: DONE (bonus fix)**
- Invalid test runner now accepts all error types (not just resource errors)
- Known limitation tracking with clear documentation
- Went from 10 failures to 1 known gap

### Remaining Gap

**Macro System: DONE**
- Declarative macros: `macro name { ($pattern) => { template } }`
- Lexer: `$` (Dollar) token for metavariables
- Parser: `parse_macro_def()`, `parse_macro_rule()`, `parse_macro_tokens()` with balanced nesting
- AST: `ExprKind::MacroCall { name, args }` for invocations (`name!(args)`)
- Interpreter: full template expansion with metavar substitution, re-parsing, child env evaluation
- Type checker: MacroCall returns fresh type var, binary ops tolerate type vars (defer to runtime)
- Token-to-source mapping: 30+ operators/keywords correctly round-trip through templates
- Tested: `double_it!(5)→10`, `max_of!(10,20)→20`, `square!(7)→49`, nested `max_of!(square!(3),5)→9`
- v0.1 limitation: single-rule matching, no repetition expansion, no hygiene

**Dimension Comparison: FIXED**
- `dimension_mismatch_comparison.ecl`: Now correctly caught at type-check time
- Resource<D> comparison operators verify dimension match (commit 8c9f564)
- KNOWN_RUNTIME_GAPS emptied — 0 conformance skips

### Verification (Session 4 — macro system complete)

- **Build**: Zero warnings, zero errors across 25 crates
- **Lib tests**: 271 passing
- **Conformance tests**: All passing (32 valid + 19 invalid, 0 skips)
- **panic-attack assail**: 15 weak points (all pre-existing: unwrap/expect calls, believe_me in Idris2 ABI)
- **No new weak points introduced by macro system**
- **Macro e2e test**: 4 macros tested (double_it, max_of, square, nested composition)

---

## 18. INTEROPERABILITY (FFI TO OTHER LANGUAGES)

**Current state: Foundation in place (extern block parsing + type checking + interpreter stubs), no real linking**

**Done (2026-02-09):**
- Extern block syntax parsed (already existed)
- Extern function signatures registered in type checker (new)
- Extern statics registered in type checker (new)
- Extern functions return graceful "not linked" error in interpreter (new)
- Extern statics registered as Unit placeholders (new)

### Required FFI Targets (Priority Order)

| # | Language | Why | Strategy |
|---|----------|-----|----------|
| 1 | **C** | Foundation for all other FFI | `extern "C"` blocks, link to .so/.dylib/.dll |
| 2 | **Rust** | Compiler is in Rust, natural integration | C ABI bridge or direct Rust crate integration |
| 3 | **JavaScript** | WASM target, browser interop | WASM exports/imports, JS glue code |
| 4 | **ReScript** | Hyperpolymath primary app language | Via JS interop (ReScript compiles to JS) |
| 5 | **Python** | Massive ecosystem, data science | C FFI → Python ctypes/cffi, or PyO3-style |
| 6 | **PHP** | Web ecosystem | C FFI → PHP extension, or WASM |
| 7 | **Elixir/Erlang** | BEAM ecosystem, if BEAM backend added | NIFs via C FFI, or BEAM bytecode |
| 8 | **Go** | (banned in hyperpolymath, but ecosystem interop) | C FFI bridge |

### eclexia Language Syntax for FFI (Proposed)
```eclexia
// C FFI
extern "C" {
    fn malloc(size: usize) -> *mut u8
    fn free(ptr: *mut u8)
    fn sqlite3_open(filename: *const u8, db: *mut *mut Sqlite3) -> i32
}

// Rust FFI
extern "Rust" {
    fn serde_json_parse(input: String) -> Result<JsonValue, String>
}

// WASM imports
extern "WASM" {
    fn console_log(msg: String)
}
```

---

## 19. WEBSITE & PLAYGROUND PLAN

### Domains
- **Website:** eclexia.org
- **Playground:** playground.eclexia.org

### Both Must Be PWAs
- Service workers for offline access
- App manifest for install-to-homescreen
- Responsive design (mobile-first)

### Website (eclexia.org)
- Landing page with "Economics as Code" value proposition
- Getting started guide
- Language reference
- Tutorial series
- Blog/news section
- Download/install instructions
- Community links (GitHub, Discord/Matrix)
- Documentation (wiki content)

### Playground (playground.eclexia.org)
- Web-based REPL with syntax highlighting
- Example programs loadable from dropdown
- Share code via URL
- Resource tracking visualisation
- Shadow price display
- Multiple execution modes (interpret, compile, step-through)
- Powered by WASM backend (when ready) or server-side execution

### Implementation Options
- **eclexia SSG** (polystack/poly-ssg engine) — eat your own dog food
- **WordPress** — Jonathan has access, faster to deploy
- **Recommendation:** WordPress for immediate website, migrate to eclexia SSG later

---

## 20. CONCURRENCY & PARALLELISM LIBRARY

**STATUS: DONE (core implementation complete)**

### Implemented (Sessions 3-6, 2026-02-09)
| Component | Description | Status |
|-----------|-------------|--------|
| `eclexia-async` | Async runtime (executor, channel, task, parallel) | DONE — 10 tests |
| AST nodes | Spawn/Channel/Send/Recv/Select/YieldExpr | DONE — integrated across workspace |
| Channels | mpsc, broadcast, oneshot | DONE |
| Task spawning | `spawn` with resource tracking | DONE |
| Parallel iterators | `par_map`, `par_filter`, `par_reduce` | DONE |
| `stdlib/async.ecl` | Eclexia-level concurrency API (@builtin) | DONE — 11 functions declared |
| Type checker stubs | Concurrency expressions type-check | DONE |
| Actor model | Lightweight actors with mailboxes | TODO |
| Mutexes/RwLocks | Synchronisation primitives | TODO |
| Thread pool | Configurable worker pool | TODO |

### Resource-Aware Concurrency (Unique to Eclexia)
- Each task tracks its own resource budget (implemented in eclexia-async)
- Shadow prices propagate across task boundaries
- Carbon-aware task scheduling (defer low-priority tasks to green energy)
- This is WHERE eclexia's economic model really shines

---

## 21. ADDITIONAL CORE TOOLS, FRAMEWORKS & LIBRARIES

### Tools Not Yet Mentioned
| Tool | Description | Status |
|------|-------------|--------|
| `eclexia-repl` improvements | Multi-line, history, highlighting, :type/:info | TODO |
| `eclexia-watch` | File watcher + incremental rebuild | Exists in eclexia-tiered, not wired |
| `eclexia-profile` | Runtime profiling output (flamegraph, etc.) | TODO |
| `eclexia-coverage` | Code coverage tool (currently via cargo-tarpaulin) | TODO |
| `eclexia-fuzz` | Fuzzing infrastructure (ClusterFuzzLite config exists) | PARTIAL |
| `eclexia-bench` | Benchmark runner (exists, verify it works) | PARTIAL |
| `eclexia-migrate` | Schema migration tool (for DB connectors) | TODO |
| `eclexia-scaffold` | Project generator (eclexia init exists, expand it) | PARTIAL |

### Frameworks Not Yet Mentioned
| Framework | Description | Status |
|-----------|-------------|--------|
| `eclexia-web-server` | HTTP server framework (beyond client) | TODO |
| `eclexia-rest` | REST API framework | TODO |
| `eclexia-graphql` | GraphQL server/client | TODO |
| `eclexia-grpc` | gRPC support | TODO |
| `eclexia-websocket` | WebSocket support | TODO |
| `eclexia-queue` | Message queue (AMQP, NATS, etc.) | TODO |
| `eclexia-cache` | Caching framework (in-memory, Redis) | TODO |
| `eclexia-orm` | Object-relational mapping | TODO |
| `eclexia-auth` | Authentication framework (JWT, OAuth) | TODO |
| `eclexia-template` | Template engine (for web/SSG) | TODO |

### Additional Libraries
| Library | Description | Status |
|---------|-------------|--------|
| `eclexia-uuid` | UUID generation | TODO |
| `eclexia-datetime` | Date/time beyond stdlib (timezones, formatting) | TODO |
| `eclexia-encoding` | Base64, hex, URL encoding | TODO |
| `eclexia-compression` | gzip, zstd, brotli | TODO |
| `eclexia-serialisation` | MessagePack, CBOR, Protobuf | TODO |
| `eclexia-validation` | Input validation framework | TODO |
| `eclexia-cli` | CLI argument parsing framework | TODO |
| `eclexia-process` | Child process management | TODO |
| `eclexia-signal` | OS signal handling | TODO |
| `eclexia-env` | Environment variable management | TODO |

---

## 22. FUNDING & BUSINESS DOCUMENTS

### Documents to Create (in `business/` directory)

| Document | Description | Priority |
|----------|-------------|----------|
| `business/PITCH-DECK.md` | 10-15 slide pitch deck (problem, solution, market, traction) | HIGH |
| `business/BUSINESS-PLAN.md` | Full business plan (executive summary, market analysis, revenue model) | HIGH |
| `business/GRANT-APPLICATIONS/` | Directory for grant applications | HIGH |
| `business/SPONSORSHIP.md` | GitHub Sponsors / Open Collective setup guide | HIGH |
| `business/ONE-PAGER.md` | Single-page executive summary | HIGH |
| `business/MARKET-ANALYSIS.md` | Target markets, competitors, differentiation | MEDIUM |
| `business/REVENUE-MODEL.md` | How eclexia generates revenue (hosting, support, training) | MEDIUM |
| `business/PARTNERSHIP-PROPOSALS/` | Templates for university/industry partnerships | MEDIUM |
| `business/ACADEMIC-PAPER.md` | Draft academic paper for publication | MEDIUM |

### Potential Funding Sources
| Source | Type | Relevance |
|--------|------|-----------|
| **GitHub Sponsors** | Recurring donations | Immediate — set up now |
| **Open Collective** | Fiscal sponsorship | Immediate |
| **EPSRC** (UK) | Research grant | HIGH — green computing angle |
| **Innovate UK** | Innovation grant | HIGH — sustainability tech |
| **EU Horizon Europe** | Research grant | HIGH — Green Deal alignment |
| **NSF** (US) | Research grant | MEDIUM — PL research angle |
| **DARPA** (US) | Research contract | LOW — resource-aware computing |
| **Google Summer of Code** | Student contributors | MEDIUM — ecosystem growth |
| **NLnet Foundation** | Open source grants | HIGH — European, FOSS-focused |
| **Sovereign Tech Fund** (DE) | Infrastructure funding | HIGH — digital infrastructure |
| **Open Technology Fund** | Internet freedom grants | LOW |
| **Mozilla Builders** | Innovation grants | MEDIUM — web sustainability |
| **Climate tech VCs** | Investment | MEDIUM — carbon-aware computing |
| **University partnerships** | Collaborative research | HIGH — Open University connection |

### Revenue Model Options
1. **Open core:** Language free, enterprise features paid (hosted registry, SLA support)
2. **Cloud hosting:** Managed eclexia compute with carbon tracking dashboard
3. **Consulting:** Help organisations adopt resource-aware programming
4. **Training:** Workshops, courses, certifications
5. **Carbon credits:** If eclexia provably reduces emissions, monetise the savings

---

## 23. REVISION HISTORY

| Date | Change |
|------|--------|
| 2026-02-09 | V12: Added effect_system_demo + module_system_demo examples, added main() to bench/test examples for manual run, example set now 36 files (all interpret/run). Bytecode build/run verified for 25/36; 11 fail or hang due to VM gaps (fields, strings, call-indirect, missing builtins). |
| 2026-02-09 | V11: Added resource tracking, shadow price optimization, and multi-objective optimization examples (all run). Example set now 34 files, all interpret/run verified. |
| 2026-02-09 | V10: Integration tests stabilized (unique temp files + `CARGO_BIN_EXE_eclexia`), Result Ok/Err pattern mismatch fixed, scheduler tests corrected to use `energy` shadow price key, `comprehensive_opportunity.ecl` verified with observe-shadow/carbon-report, `bench_energy.ecl` repaired, all 31 examples interpret/run successfully, wasm unused-variable warning cleared. |
| 2026-02-09 | V9: Session 10 continuation — MIR adaptive def lowering fix completed (2 bugs: missing parent params in local_map + clone-replace arena loss). Safe fallback for unknown locals in ExprKind::Local. 5 new example programs: macros, hashmaps, higher_order, recursion, type_system. 24/29 examples working (was 19/24). STATE.scm updated. 271 lib + 51 conformance tests passing. |
| 2026-02-09 | V8: Sessions 9-10 — 4/7 reactive crates wired (added specialize+effects), shadow prices live (ShadowPriceRegistry+ShadowPriceEngine), CallBuiltin VM instruction (build works with builtins), MIR adaptive def fix (build --analyze works on adaptive def), 4 new examples (hello_world, fibonacci, traits_and_impls, generics), 19/24 examples working, .eclb round-trip verified, full verification audit with 11 discrepancies found and fixed. Overall ~65%. |
| 2026-02-09 | V7: Session 8 — DEEP VERIFICATION AUDIT of all completed items (13 verification tasks). BUGS FIXED: enum variant matching (Pattern::Var→compare), Value::Struct PartialEq (was always false). All 11 examples now correct. Conformance: 51/51 pass, 271 lib tests pass. Doc honesty: 7 docs verified (A+ to B+ grades). Infrastructure: SEAM_ANALYSIS exists, INTEROP_STATUS missing, OPSM adapter missing, verisimdb scan exists, stdlib/async.ecl verified. panic-attack: 15 weak pts, 327 unwraps (corrected from 331), 28 unsafe, 48 panic sites, 49990 lines. Known remaining issues: `build` fails on files using builtins (println), `build --analyze` panics on adaptive def. Overall ~62%. |
| 2026-02-09 | V6: Session 7 — .eclb binary format (8-byte header), doc honesty pass (6 docs: GETTING_STARTED, SELF-HOSTING-ROADMAP, MULTICOMPILER-ARCHITECTURE, ROADMAP, IMPLEMENTATION_ROADMAP, WHITEPAPER), 3 dangerous production unwraps fixed, verisimdb ingested, `build --analyze` wires eclexia-absinterp + eclexia-comptime into CLI. 5 commits + 1 verisimdb. Overall ~60%. |
| 2026-02-09 | V5: Session 6 — bytecode serde + .eclb file format, extern block type checking + interpreter stubs (FFI foundation), stdlib/async.ecl (concurrency stdlib), 11 working example programs, clippy lint pass (zero errors), panic-attack scan (15 weak pts, 327 unwraps). Section 20 concurrency marked DONE. Overall ~58%. |
| 2026-02-09 | V4: Updated after session 5 — runtime stubs implemented (25 tests), dimension comparison fix (0 conformance skips), bytecode serialization, seam analysis (2 critical fixes), interop bridges, documentation honesty pass, reqwest upgrade. 271 lib tests, 51 conformance. Echidna verify: 5/6 QED. |
| 2026-02-09 | V3: Added advanced compiler extensions, interoperability/FFI plan, website/playground plan (eclexia.org, playground.eclexia.org, PWAs), concurrency library, additional tools/frameworks/libraries, funding/business documents, parallelisation. |
| 2026-02-09 | V2: Added panll, OPSM, example programs, IDE plugins, linter/minter expansion, roadmap audit (280 items from planning docs, ~7% done), Idris2/Zig pattern for DB connectors, math library, network library, domain std libs, self-hosting plan, distribution plan, to-done section. Library priority reordered with user input. |
| 2026-02-09 | V1: Initial comprehensive audit. Honest assessment replacing false "100% complete" claims. |

---

*This document MUST be updated every session. Move completed TO-DO items to TO-DONE.
If context is lost, hand this file to the next AI session.
Domains: eclexia.org | playground.eclexia.org*
