# Eclexia - Quick Status Reference

**Last Updated:** 2026-02-24
**Completion:** Alpha — Core compiler functional, all SONNET completion tasks complete
**Build:** Passing (25 crates, zero clippy warnings)
**Tests:** Local quality gate passing (docs, fmt, lint, unit, conformance, integration, p2p, e2e, benchmarks)

---

## What Works

### Compiler Pipeline
- Lexer with dimensional literals (893 lines, 95+ tokens)
- Pratt parser with macro definition support (3106+ lines)
- Hindley-Milner type checker with Robinson unification (2210 lines)
- HIR lowering with concurrency expressions (Spawn, Channel, Send, Recv, Select, Yield, MacroCall)
- MIR with optimizations (constant propagation, dead code elimination)
- Bytecode generator with concurrency builtins
- Stack-based VM (934 lines) with 18 unit tests
- Tree-walking interpreter (separate path, 28 builtin tests, concurrency support via tokio)

### Runtime System
- Shadow price registry and forecasting (real defaults: energy=0.000033, time=0.001, carbon=0.00005)
- Resource tracking: energy, time, memory, carbon
- Adaptive decision engine with budget enforcement (7 tests)
- Scheduler: shadow-price-aware task scheduling with defer/reject/run (4 tests)
- Profiler: wall-clock profiling with energy/carbon estimation + RSS memory tracking (6 tests)
- Carbon monitor: grid intensity with Green/Yellow/Red signals (7 tests)
- Shadow price engine: utilization-curve LP duality pricing (8+ tests)

### Backends (All 3 generate real code)
- **WASM:** Generates valid .wasm binaries via wasm-encoder; complex types (tuples, arrays, structs) as i32 linear memory pointers; WASI preview1 imports (fd_write, clock_time_get, args); 24 tests
- **LLVM:** Generates textual .ll IR files; runtime linking via eclexia-rt-native static library (5 C-compatible symbols); 21 tests
- **Cranelift:** Real JIT for simple integer functions; string data sections; Range/RangeInclusive support; fallback estimation for complex ops; 8 tests

### Standard Library (~85%)
- Core types: Option, Result
- Collections: Vec, HashMap, HashSet, SortedMap, Queue, PriorityQueue
- Math: trig, log, rounding, number theory
- I/O operations: read_file, write_file, file_exists
- Text processing: trim, split, contains, uppercase, lowercase
- Time: Duration, Instant, DateTime, sleep, measure
- Async: task_spawn, task_await, channel_create, channel_send, channel_recv (wired to VM + interpreter)

### Developer Tooling
- CLI: build (--analyze, --target wasm/llvm), run, check, fmt, lint, repl, init, test, bench, debug, doc, install, watch, disasm, interop
- REPL with expression evaluation
- Testing framework (#[test] attributes)
- Benchmarking framework (#[bench] attributes)
- Package manager: manifest parsing + dependency resolution + registry server stub
- LSP server: diagnostics, symbols, navigation, hover, completion, rename, formatting
- Formatter: AST pretty printer
- Linter: 10+ rules
- Debugger: Interactive with breakpoints, step, stack inspection
- VSCode extension: Syntax highlighting + LSP integration
- Interop bridge validator: `eclexia interop check` validates 4 language bridges

### Testing
- 507 total tests passing (0 failures)
- 446 library tests passing (across all crates)
- 32/32 valid conformance tests passing
- 19/19 invalid conformance tests correctly rejecting (0 skips)
- 11 property-based tests (1000+ generated cases each)
- 0 clippy warnings

### Formal Verification (Partial)
- Coq proofs: Typing.v (0 Admitted), ShadowPrices.v (4 Admitted — deep LP theory)
- Agda proofs: ResourceTracking.agda
- 4 remaining Admitted theorems are genuinely hard LP proofs (strong duality, dual variables, complementary slackness)

---

## What Does NOT Work Yet

- **Native compilation end-to-end:** LLVM backend generates .ll but linking to runtime is manual (static library exists, automatic linking not wired)
- **WASM GC:** No garbage collection in WASM linear memory; bump allocator defined but not yet wired
- **Runtime system metrics:** scheduler/profiler/carbon/shadow implemented but not wired to real OS metrics (except RSS memory on Linux)
- **Macro expansion in HIR:** MacroCall lowered to HIR variant but MIR emits Nop — only interpreter supports macro eval
- **Measured benchmarks:** None — all performance claims are projections
- **Package registry deployment:** Server stub exists (filesystem backend, 3 routes), not deployed
- **Formal proofs:** 4 Admitted in ShadowPrices.v (strong duality, dual variables, slack/zero, positive/binding)

---

## Security Status

- **panic-attack (2026-02-24):** 6 weak points, 0 critical (Idris `believe_me` removed)
- **Production unwraps:** 163 static `unwrap/expect` sites remain across parser/vm/registry paths
- **Clippy warnings:** 0 (all resolved)
- **Unsafe blocks:** 32 (primarily FFI/runtime-native boundaries)
- **Known conformance skip:** `stack_overflow_deep_recursion.ecl` skipped by default to avoid intentional `SIGABRT` core dumps in routine QA runs

---

## Quick Commands

```bash
# Build everything
cargo build --workspace

# Run all library tests
cargo test --workspace --lib

# Run conformance tests
cargo test -p eclexia --test conformance_tests

# Full test suite (507 tests)
cargo test --workspace

# Check for warnings
cargo clippy --workspace

# Try the REPL
cargo run -- repl

# Run an example
cargo run -- run examples/fibonacci_adaptive.ecl

# Validate interop bridges
cargo run -- interop check

# Security scan
just panic-attack
```

---

## Key Files

| Area | Files |
|------|-------|
| Compiler | compiler/eclexia-{lexer,parser,typeck,hir,mir,codegen}/ |
| Interpreter | compiler/eclexia-interp/ |
| Runtime | runtime/eclexia-runtime/ |
| Native Runtime | runtime/eclexia-rt-native/ (static lib for LLVM linking) |
| Registry Server | runtime/eclexia-registry-server/ |
| Backends | compiler/eclexia-{cranelift,llvm,wasm}/ |
| Tooling | compiler/eclexia-{fmt,lint,debugger,doc,lsp}/ |
| Tests | tests/conformance/{valid,invalid}/ |
| Formal | formal/{coq,agda}/ |
| Stdlib | stdlib/ |
| Interop | interop/*.toml, compiler/eclexia/src/interop.rs |

---

**Honest assessment:** Eclexia is a working alpha compiler with a functional pipeline
from source to bytecode VM, with three real code-generation backends (WASM, LLVM, Cranelift).
The economics-as-code concepts (shadow prices, adaptive functions, resource tracking) are
implemented in the runtime with real defaults and tests. All 18 SONNET completion
tasks are done. Not production-ready. Not feature-complete. Active development.
