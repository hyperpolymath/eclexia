# Eclexia Implementation Plan: LLVM Backend First

**Date:** 2026-02-07
**Goal:** Ship production-ready LLVM backend in 3-4 months
**Status:** 🟡 Starting implementation

---

## Priority 1: LLVM Backend (Weeks 1-12)

**Why this matters:** Without native code generation, Eclexia is a research toy. LLVM unlocks production deployment.

### Week 1-2: Foundation & Setup

**Immediate Actions (TODAY):**

1. ✅ Install LLVM dependencies
2. ✅ Set up `eclexia-codegen-llvm` crate
3. ✅ Write minimal "Hello, World" LLVM IR generator
4. ✅ Verify: Compile simple Eclexia program → native binary
5. ✅ Benchmark: Compare to bytecode VM

**Deliverable:** Proof-of-concept that generates working native code

---

### Week 3-4: Type Lowering

**Tasks:**
- [ ] Map Eclexia types → LLVM types
  - `Int` → `i64`
  - `Float` → `f64`
  - `Bool` → `i1`
  - `String` → `ptr + len` (fat pointer)
  - `Option<T>` → tagged union
  - Structs → LLVM structs
  - Functions → LLVM function types
- [ ] Handle dimensional types (Energy, Carbon, Duration)
  - Compile-time: Validate units
  - Runtime: Store as f64 (same as Float)
- [ ] Implement memory layout calculation
- [ ] Add alignment/padding for structs

**Deliverable:** Type-safe code generation for all Eclexia types

---

### Week 5-6: Function Codegen

**Tasks:**
- [ ] Regular function codegen
  - Parameters, return values
  - Local variables (stack allocation)
  - Function calls
  - Return statements
- [ ] Control flow
  - If/else → LLVM br/switch
  - While loops → LLVM br + phi nodes
  - For loops → desugared to while
- [ ] Pattern matching → switch + destructuring
- [ ] Closures → function pointers + environment capture

**Deliverable:** Full function compilation, control flow works

---

### Week 7-8: Adaptive Functions (Core Innovation)

**Tasks:**
- [ ] Generate separate functions for each `@solution`
- [ ] Create dispatch table (array of function pointers)
- [ ] Generate wrapper function:
  1. Call shadow price scheduler
  2. Index into dispatch table
  3. Call selected function
- [ ] Implement shadow price scheduler in runtime library
- [ ] Resource metadata encoding (LLVM metadata nodes)

**Example:**
```eclexia
adaptive def foo(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "a": @provides: energy: 5J { n * 2 }
    @solution "b": @provides: energy: 50J { n * n }
}
```

**Generated LLVM IR (conceptual):**
```llvm
define i64 @foo_solution_a(i64 %n) {
  %result = mul i64 %n, 2
  ret i64 %result
}

define i64 @foo_solution_b(i64 %n) {
  %result = mul i64 %n, %n
  ret i64 %result
}

define i64 @foo(i64 %n) {
  ; Get shadow prices from runtime
  %prices = call ptr @eclexia_runtime_get_shadow_prices()

  ; Select solution (calls linear programming solver)
  %solution_id = call i32 @eclexia_runtime_select_solution(
    ptr @foo_metadata,
    ptr %prices
  )

  ; Dispatch
  switch i32 %solution_id, label %default [
    i32 0, label %call_a
    i32 1, label %call_b
  ]

call_a:
  %result_a = call i64 @foo_solution_a(i64 %n)
  br label %done

call_b:
  %result_b = call i64 @foo_solution_b(i64 %n)
  br label %done

done:
  %result = phi i64 [ %result_a, %call_a ], [ %result_b, %call_b ]
  ret i64 %result
}
```

**Deliverable:** Adaptive functions compile and dispatch correctly

---

### Week 9-10: Resource Tracking

**Tasks:**
- [ ] Implement runtime resource tracking library
  - RAPL (Intel/AMD energy counters)
  - PowerMetrics (macOS)
  - Clock for timing
  - Carbon calculation (energy × grid intensity)
- [ ] Insert tracking hooks in generated code
  - Before function: `call @eclexia_runtime_start_tracking()`
  - After function: `call @eclexia_runtime_stop_tracking()`
- [ ] Zero-cost when unused (LLVM dead-code elimination)
- [ ] Expose to user: `current_energy()`, `current_carbon()`

**Deliverable:** Resource tracking works, minimal overhead

---

### Week 11-12: Optimization & Cross-Compilation

**Tasks:**
- [ ] Run LLVM optimization passes
  - Constant folding
  - Dead code elimination
  - Inlining (especially for zero-cost abstractions)
  - SIMD vectorization
- [ ] Cross-compilation support
  - x86-64-unknown-linux-gnu
  - aarch64-apple-darwin (M1/M2/M3)
  - aarch64-unknown-linux-gnu (AWS Graviton)
  - x86_64-pc-windows-msvc
- [ ] Link against runtime library
- [ ] Static vs dynamic linking options

**Deliverable:** Production-quality binaries for major platforms

---

## Priority 2: Runtime Library (Parallel Track)

**While building LLVM backend, implement runtime in Rust:**

### Runtime Components

1. **Shadow Price Scheduler** (`runtime/src/scheduler.rs`)
   ```rust
   pub fn select_solution(
       solutions: &[Solution],
       constraints: &[Constraint],
       shadow_prices: &[f64],
   ) -> usize {
       // Linear programming solver (good_lp crate)
       // Returns index of Pareto-optimal solution
   }
   ```

2. **Resource Tracker** (`runtime/src/tracking.rs`)
   ```rust
   pub fn start_tracking() -> ResourceSnapshot;
   pub fn stop_tracking(start: ResourceSnapshot) -> ResourceUsage;
   pub fn current_energy() -> f64;  // Joules
   pub fn current_carbon() -> f64;  // gCO2e
   ```

3. **Carbon APIs** (`runtime/src/carbon.rs`)
   ```rust
   pub fn get_grid_carbon_intensity(location: Location) -> Result<f64>;
   pub fn get_forecast(location: Location, hours: u32) -> Result<Vec<CarbonForecast>>;
   ```

---

## Development Setup

### Prerequisites

```bash
# Install LLVM 17 (or latest)
# macOS
brew install llvm@17

# Fedora
sudo dnf install llvm-devel llvm-static clang

# Ubuntu
sudo apt install llvm-17-dev libclang-17-dev
```

### Rust Dependencies

Add to `Cargo.toml`:
```toml
[dependencies]
# LLVM bindings
inkwell = { version = "0.4", features = ["llvm17-0"] }

# Linear programming (shadow price optimization)
good_lp = "1.8"

# Energy measurement
rapl = "0.1"  # Intel/AMD energy counters

# HTTP client (for carbon APIs)
reqwest = { version = "0.11", features = ["json"] }
tokio = { version = "1", features = ["full"] }
```

---

## Milestone Checklist

### Milestone 1: Hello, LLVM (Week 2)
- [ ] Generate LLVM IR for `def main() { println("Hello") }`
- [ ] Compile to native binary
- [ ] Run successfully
- [ ] Benchmark vs bytecode VM

### Milestone 2: Fibonacci (Week 4)
- [ ] Generate LLVM IR for recursive fibonacci
- [ ] Control flow (if/else) works
- [ ] Function calls work
- [ ] Performance competitive with Rust

### Milestone 3: Adaptive Fibonacci (Week 8)
- [ ] Two solutions (efficient vs naive)
- [ ] Shadow price selection works
- [ ] Runtime picks optimal solution
- [ ] Overhead < 50ns

### Milestone 4: Resource Tracked Fibonacci (Week 10)
- [ ] Energy measurement works (RAPL)
- [ ] `current_energy()` returns accurate value
- [ ] Zero overhead when tracking disabled
- [ ] Benchmark shows negligible impact

### Milestone 5: Multi-Target (Week 12)
- [ ] Cross-compile to x86-64 Linux
- [ ] Cross-compile to ARM64 macOS
- [ ] Cross-compile to Windows
- [ ] Performance within 1.5x of Rust

---

## Success Criteria

**Technical:**
- ✅ Compiles all 32 conformance tests
- ✅ Passes all test suite
- ✅ Performance ≤ 1.5x Rust
- ✅ Binary size ≤ 10MB (static)
- ✅ Supports 3+ platforms

**User-Facing:**
- ✅ `eclexia build app.ecl` produces native binary
- ✅ `eclexia build --target aarch64-apple-darwin` cross-compiles
- ✅ Resource tracking works out-of-box (RAPL on Linux, PowerMetrics on macOS)
- ✅ Adaptive functions ~10ns overhead
- ✅ Documentation explains usage

---

## Next Steps (IMMEDIATE)

### Today (Feb 7):
1. ✅ Create this implementation plan
2. ⏳ Set up LLVM development environment
3. ⏳ Scaffold `compiler/eclexia-codegen-llvm/` crate
4. ⏳ Write minimal "Hello, World" IR generator

### Tomorrow (Feb 8):
5. ⏳ Get first native binary compiling
6. ⏳ Benchmark vs bytecode VM
7. ⏳ Create GitHub issues for week-by-week tasks

### This Week:
8. ⏳ Type lowering (Int, Float, Bool, String)
9. ⏳ Function codegen (parameters, return, calls)
10. ⏳ Hello, World → Fibonacci working natively

---

## Risk Mitigation

### Risk 1: LLVM Complexity
**Mitigation:** Start simple (integers, basic functions). Build incrementally. Use inkwell abstractions.

### Risk 2: Performance Regression
**Mitigation:** Benchmark every week. Profile with `perf`. Use LLVM optimization passes aggressively.

### Risk 3: Cross-Platform Issues
**Mitigation:** Test on Linux first (easiest), then macOS, then Windows. Use CI for all platforms.

### Risk 4: Resource Tracking Accuracy
**Mitigation:** Validate against external tools (Intel VTune, powermetrics). Document limitations.

---

## Resources

### Learning LLVM
- **Inkwell Tutorial:** https://github.com/TheDan64/inkwell
- **LLVM Language Reference:** https://llvm.org/docs/LangRef.html
- **Kaleidoscope Tutorial:** https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/

### Reference Implementations
- **Rust compiler:** How rustc uses LLVM
- **Zig compiler:** Similar approach (self-hosted, LLVM backend)
- **Crystal compiler:** Another Rust → LLVM pipeline

### Debugging
- **llvm-dis:** Disassemble LLVM bitcode to IR
- **opt:** Run optimization passes standalone
- **llc:** Lower LLVM IR to assembly
- **lldb:** Debug generated binaries

---

## Communication

### Weekly Updates
Post progress to:
- GitHub Discussions (technical details)
- Discord #development (community)
- Twitter (public milestones)

### Blockers
If stuck for >4 hours:
- Post to Discord #help
- Create GitHub issue with "blocked" label
- Reach out to LLVM community (forum.llvm.org)

---

## The Goal

**In 12 weeks:**
- Eclexia compiles to native code via LLVM
- Adaptive functions work with real shadow price optimization
- Resource tracking measures energy/carbon
- Cross-compiles to x86-64, ARM64, Windows
- Performance competitive with Rust (≤1.5x)

**Then:** Self-hosting, domain libraries, world domination. 🌍

**Let's build this.** 🚀
