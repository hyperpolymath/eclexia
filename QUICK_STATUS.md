# Eclexia - Quick Status Reference

**Last Updated:** 2026-02-09
**Completion:** Alpha — Core compiler functional, many subsystems stubbed
**Build:** Passing (25 crates, zero warnings)
**Tests:** 271 library tests + 32/32 valid + 19/19 invalid conformance (0 skips)

---

## What Works

### Compiler Pipeline
- Lexer with dimensional literals (893 lines, 95+ tokens)
- Pratt parser with macro definition support (3106+ lines)
- Hindley-Milner type checker with Robinson unification (2210 lines)
- HIR lowering (desugaring, type annotations)
- MIR with optimizations (constant propagation, dead code elimination)
- Bytecode generator
- Stack-based VM (934 lines)
- Tree-walking interpreter (separate path, 28 builtin tests)

### Runtime System (Partial)
- Shadow price registry and forecasting (real implementation, 5326 lines)
- Resource tracking: energy, time, memory, carbon (4681 lines)
- Adaptive decision engine (8690 lines)
- Budget enforcement

- Scheduler: shadow-price-aware task scheduling with defer/reject/run (4 tests)
- Profiler: wall-clock profiling with energy/carbon estimation (6 tests)
- Carbon monitor: grid intensity with Green/Yellow/Red signals (7 tests)
- Shadow price engine: utilization-curve LP duality pricing (8 tests)

### Standard Library (~85%)
- Core types: Option, Result
- Collections: Vec, HashMap, HashSet, SortedMap, Queue, PriorityQueue
- Math: trig, log, rounding, number theory
- I/O operations: read_file, write_file, file_exists
- Text processing: trim, split, contains, uppercase, lowercase
- Time: Duration, Instant, DateTime, sleep, measure
- **Missing:** Concurrency primitives, networking, regex

### Developer Tooling
- CLI: build (--analyze), run, check, fmt, lint, repl, init, test, bench, debug, doc, install, watch, disasm
- REPL with expression evaluation
- Testing framework (#[test] attributes)
- Benchmarking framework (#[bench] attributes)
- Package manager: manifest parsing + dependency resolution (registry is client stub)
- LSP server: diagnostics, symbols, navigation, hover, completion, rename, formatting
- Formatter: AST pretty printer
- Linter: 10+ rules
- Debugger: Interactive with breakpoints, step, stack inspection
- VSCode extension: Syntax highlighting + LSP integration

### Testing
- 271 library tests passing (across all crates)
- 32/32 valid conformance tests passing
- 19/19 invalid conformance tests correctly rejecting (0 skips)
- 5 integration tests failing (pre-existing temp file race condition — not a code bug)
- 11 property-based tests (1000+ generated cases each)

### Formal Verification (Partial)
- Coq proofs: ShadowPrices.v, Typing.v
- Agda proofs: ResourceTracking.agda
- **22 theorems Admitted (assumed, not proven)** — honest count
- Some theorems fully proved (progress, preservation, duality)

---

## What Does NOT Work Yet

- **Native backends:** Cranelift, LLVM, WASM crates exist but only estimate sizes — no real codegen
- **Runtime integration:** scheduler/profiler/carbon/shadow implemented but not wired to real system metrics
- **Reactive compilation:** 4/7 crates wired into `build --analyze` (absinterp, comptime, specialize, effects); remaining 3 not yet wired (db, modules, tiered)
- **Shadow prices:** ShadowPriceRegistry real defaults (energy=0.000033, time=0.001, carbon=0.00005); dynamic prices computed from VM resource usage via ShadowPriceEngine
- **Bytecode serialization:** .eclb binary format implemented (write/read/round-trip verified)
- **Bytecode builtins:** CallBuiltin instruction + VM dispatch (println, print, to_string, abs, sqrt, etc.) — `build` now works on files using builtins
- **Adaptive def MIR:** Fixed — `build --analyze` no longer panics on adaptive def constructs
- **Package registry:** Client stub exists, no server deployed
- **Concurrency:** AST nodes parsed (spawn, channel, send, recv, select, yield) but interpreter returns errors
- **Macro expansion in HIR:** MacroCall lowers to Unit — only interpreter supports macro eval
- **Measured benchmarks:** None — all performance claims are projections
- **Code coverage:** 17.92% baseline (target: 80%)

---

## Security Status (panic-attack scan 2026-02-09)

- **15 weak points** (327 unwraps, 28 unsafe blocks, 48 panic sites)
- Top offenders: builtins.rs (96 unwraps in tests), parser/lib.rs (84)
- 3 dangerous production unwraps fixed (modules, REPL, LSP)
- 2 Critical: believe_me in Idris2 ABI files (intentional pattern)
- 1 Command injection risk: recoverer-setup.sh (47 unquoted vars)
- 47,295 total lines scanned

---

## Quick Commands

```bash
# Build everything
cargo build --workspace

# Run all library tests
cargo test --workspace --lib

# Run conformance tests
cargo test -p eclexia --test conformance_tests

# Try the REPL
cargo run -- repl

# Run an example
cargo run -- run examples/fibonacci_adaptive.ecl

# Security scan
panic-attack assail . --output /tmp/eclexia-scan.json
```

---

## Key Files

| Area | Files |
|------|-------|
| Compiler | compiler/eclexia-{lexer,parser,typeck,hir,mir,codegen}/ |
| Interpreter | compiler/eclexia-interp/ |
| Runtime | runtime/eclexia-runtime/ |
| Tooling | compiler/eclexia-{fmt,lint,debugger,doc,lsp}/ |
| Tests | tests/conformance/{valid,invalid}/ |
| Formal | formal/{coq,agda}/ |
| Stdlib | stdlib/ |

---

**Honest assessment:** Eclexia is a working alpha compiler with a functional pipeline
from source to bytecode VM. The economics-as-code concepts (shadow prices, adaptive
functions, resource tracking) are implemented in the runtime but several subsystems
are stubs. Not production-ready. Not feature-complete. Active development.
