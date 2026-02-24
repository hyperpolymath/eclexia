# GitHub Issues: LLVM Backend Implementation

**Purpose:** Track LLVM backend development week-by-week

**Labels:**
- `P0-critical` - Blocks everything else
- `P1-high` - Important for MVP
- `P2-medium` - Nice to have
- `backend-llvm` - LLVM backend work
- `runtime` - Runtime library work
- `testing` - Test infrastructure

---

## Week 1-2: Foundation (Issues #1-10)

### Issue #1: Set up LLVM development environment
**Priority:** P0-critical
**Labels:** backend-llvm, good-first-issue

**Description:**
Set up LLVM development environment for all contributors.

**Tasks:**
- [ ] Document LLVM installation (macOS, Linux, Windows)
- [ ] Add `inkwell` dependency to Cargo.toml
- [ ] Verify LLVM 17 works on all platforms
- [ ] Create simple "Hello, LLVM" test (generate IR, compile, run)
- [ ] Add CI job to test LLVM builds

**Acceptance Criteria:**
- Documentation in CONTRIBUTING.md
- CI passes on all platforms
- Simple test binary compiles and runs

---

### Issue #2: Create eclexia-codegen-llvm crate structure
**Priority:** P0-critical
**Labels:** backend-llvm

**Description:**
Scaffold the LLVM backend crate with basic infrastructure.

**Tasks:**
- [ ] Create `compiler/eclexia-codegen-llvm/` directory
- [ ] Add `Cargo.toml` with inkwell dependency
- [ ] Create `src/lib.rs` with `LLVMBackend` struct
- [ ] Implement `Backend` trait for `LLVMBackend`
- [ ] Add to workspace members in root `Cargo.toml`

**File Structure:**
```
compiler/eclexia-codegen-llvm/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Main backend struct
│   ├── types.rs         # Type lowering
│   ├── functions.rs     # Function codegen
│   ├── expressions.rs   # Expression codegen
│   ├── adaptive.rs      # Adaptive function handling
│   └── runtime.rs       # Runtime library integration
└── tests/
    └── integration.rs
```

**Acceptance Criteria:**
- Crate compiles
- Implements `Backend` trait
- Can be instantiated (even if empty)

---

### Issue #3: Minimal Hello World LLVM IR generation
**Priority:** P0-critical
**Labels:** backend-llvm, milestone-1

**Description:**
Generate LLVM IR for the simplest possible Eclexia program and compile to native binary.

**Input:**
```eclexia
def main() -> Unit {
    println("Hello, LLVM!")
}
```

**Expected LLVM IR:**
```llvm
declare i32 @puts(ptr)

define i32 @main() {
  %str = getelementptr [12 x i8], ptr @.str.0, i32 0, i32 0
  call i32 @puts(ptr %str)
  ret i32 0
}

@.str.0 = private unnamed_addr constant [12 x i8] c"Hello, LLVM!\00"
```

**Tasks:**
- [ ] Parse MIR for `main` function
- [ ] Generate `@main` LLVM function
- [ ] Generate string constant
- [ ] Call `puts` from libc
- [ ] Link against libc
- [ ] Produce executable binary

**Acceptance Criteria:**
- `eclexia build hello.ecl --backend llvm` produces binary
- Running `./hello` prints "Hello, LLVM!"
- Binary size < 50KB (statically linked)

---

### Issue #4: Benchmark LLVM vs Bytecode VM
**Priority:** P1-high
**Labels:** backend-llvm, performance

**Description:**
Establish performance baseline for LLVM backend.

**Benchmarks:**
1. Hello World (compile time + binary size)
2. Fibonacci (recursive, n=40) - runtime
3. Array sum (1M elements) - runtime
4. String concatenation (10K iterations) - runtime

**Tasks:**
- [ ] Create benchmark suite in `benches/`
- [ ] Run on bytecode VM (baseline)
- [ ] Run on LLVM backend
- [ ] Document results in `BENCHMARKS.md`
- [ ] Set CI to track regression

**Acceptance Criteria:**
- LLVM backend ≥ 10x faster than bytecode VM for fibonacci
- Compile time documented
- CI fails if performance regresses >20%

---

## Week 3-4: Type Lowering (Issues #5-8)

### Issue #5: Implement primitive type lowering
**Priority:** P0-critical
**Labels:** backend-llvm, types

**Description:**
Map Eclexia primitive types to LLVM types.

**Mapping:**
| Eclexia Type | LLVM Type | Size |
|--------------|-----------|------|
| `Int` | `i64` | 8 bytes |
| `Float` | `f64` | 8 bytes |
| `Bool` | `i1` | 1 bit |
| `Unit` | `void` | 0 bytes |
| `String` | `{ptr, i64}` | 16 bytes (fat pointer) |

**Tasks:**
- [ ] Implement `lower_type()` function in `types.rs`
- [ ] Add tests for each primitive type
- [ ] Handle `Option<T>` (tagged union: `{i1, T}`)
- [ ] Document type layout in comments

**Acceptance Criteria:**
- All primitive types lower correctly
- Tests pass
- Documentation explains memory layout

---

### Issue #6: Implement struct type lowering
**Priority:** P1-high
**Labels:** backend-llvm, types

**Description:**
Lower Eclexia structs to LLVM struct types with correct layout.

**Example:**
```eclexia
struct Point {
    x: Int,
    y: Int,
}
```

**LLVM:**
```llvm
%Point = type { i64, i64 }
```

**Tasks:**
- [ ] Generate LLVM struct types
- [ ] Calculate field offsets
- [ ] Handle alignment/padding
- [ ] Support nested structs
- [ ] Add GEP (GetElementPtr) for field access

**Acceptance Criteria:**
- Structs compile correctly
- Field access works (`point.x`)
- Memory layout matches Rust (for ABI compat)

---

### Issue #7: Implement dimensional type handling
**Priority:** P2-medium
**Labels:** backend-llvm, types

**Description:**
Handle dimensional types (Energy, Carbon, Duration) - these are compile-time validated, runtime stored as f64.

**Strategy:**
- Compile-time: Validate dimensional analysis in type checker
- Runtime: Erase to `f64` (same as `Float`)

**Tasks:**
- [ ] Lower `Energy`, `Carbon`, `Duration` to `f64`
- [ ] Ensure type checker validates units before codegen
- [ ] Add tests for unit conversions

**Acceptance Criteria:**
- Dimensional types compile to f64
- No runtime overhead vs plain Float
- Type checker catches unit errors

---

### Issue #8: Implement function type lowering
**Priority:** P1-high
**Labels:** backend-llvm, types

**Description:**
Lower Eclexia function types to LLVM function types.

**Example:**
```eclexia
def add(a: Int, b: Int) -> Int
```

**LLVM:**
```llvm
define i64 @add(i64 %a, i64 %b)
```

**Tasks:**
- [ ] Lower function signatures
- [ ] Handle multiple parameters
- [ ] Handle return types (including `Unit` → `void`)
- [ ] Handle closures (function pointer + environment)

**Acceptance Criteria:**
- Functions compile with correct signatures
- Can call functions from other functions
- Closures work (capture environment)

---

## Week 5-6: Function Codegen (Issues #9-14)

### Issue #9: Implement function prologue/epilogue
**Priority:** P0-critical
**Labels:** backend-llvm, codegen

**Description:**
Generate function entry/exit code.

**Tasks:**
- [ ] Create LLVM function from MIR
- [ ] Allocate stack space for locals (alloca)
- [ ] Generate return statement
- [ ] Handle multiple return paths (phi nodes)

**Example:**
```eclexia
def add(a: Int, b: Int) -> Int {
    let result = a + b
    result
}
```

**LLVM:**
```llvm
define i64 @add(i64 %a, i64 %b) {
entry:
  %result = alloca i64
  %sum = add i64 %a, %b
  store i64 %sum, ptr %result
  %ret = load i64, ptr %result
  ret i64 %ret
}
```

**Acceptance Criteria:**
- Functions compile and return correct values
- Stack allocation works
- Tests pass

---

### Issue #10: Implement arithmetic operations
**Priority:** P0-critical
**Labels:** backend-llvm, codegen

**Description:**
Generate LLVM IR for binary operations (+, -, *, /, %).

**Tasks:**
- [ ] Integer arithmetic (`add`, `sub`, `mul`, `sdiv`, `srem`)
- [ ] Float arithmetic (`fadd`, `fsub`, `fmul`, `fdiv`)
- [ ] Handle overflow checking (optional)
- [ ] Comparison operations (`icmp`, `fcmp`)
- [ ] Boolean operations (`and`, `or`, `xor`, `not`)

**Acceptance Criteria:**
- All binary ops work
- Integer overflow behavior documented
- Float operations follow IEEE 754

---

### Issue #11: Implement control flow (if/else)
**Priority:** P0-critical
**Labels:** backend-llvm, codegen

**Description:**
Generate LLVM basic blocks for if/else statements.

**Example:**
```eclexia
def abs(x: Int) -> Int {
    if x < 0 {
        -x
    } else {
        x
    }
}
```

**LLVM:**
```llvm
define i64 @abs(i64 %x) {
entry:
  %cond = icmp slt i64 %x, 0
  br i1 %cond, label %then, label %else

then:
  %neg_x = sub i64 0, %x
  br label %merge

else:
  br label %merge

merge:
  %result = phi i64 [ %neg_x, %then ], [ %x, %else ]
  ret i64 %result
}
```

**Tasks:**
- [ ] Create basic blocks for then/else/merge
- [ ] Generate conditional branch (`br`)
- [ ] Generate phi nodes for merging results
- [ ] Handle nested if/else

**Acceptance Criteria:**
- If/else compiles correctly
- Phi nodes merge values properly
- Nested conditions work

---

### Issue #12: Implement loops (while, for)
**Priority:** P1-high
**Labels:** backend-llvm, codegen

**Description:**
Generate LLVM IR for while loops (for loops desugar to while).

**Example:**
```eclexia
def sum(n: Int) -> Int {
    let mut total = 0
    let mut i = 0
    while i < n {
        total = total + i
        i = i + 1
    }
    total
}
```

**Tasks:**
- [ ] Create loop header, body, exit blocks
- [ ] Generate loop condition check
- [ ] Generate phi nodes for loop variables
- [ ] Handle break/continue (if supported)

**Acceptance Criteria:**
- While loops compile
- Loop variables update correctly
- Infinite loops can be written (for testing)

---

### Issue #13: Implement function calls
**Priority:** P0-critical
**Labels:** backend-llvm, codegen

**Description:**
Generate LLVM `call` instructions for function calls.

**Tasks:**
- [ ] Generate call instruction
- [ ] Pass arguments correctly (registers vs stack)
- [ ] Handle return values
- [ ] Support recursion
- [ ] Handle indirect calls (function pointers)

**Acceptance Criteria:**
- Recursive fibonacci works
- Mutual recursion works
- Indirect calls work (for closures)

---

### Issue #14: Implement pattern matching
**Priority:** P2-medium
**Labels:** backend-llvm, codegen

**Description:**
Lower pattern matching to LLVM switch + destructuring.

**Example:**
```eclexia
match option {
    Some(x) => x,
    None => 0,
}
```

**LLVM:**
```llvm
; Check tag (first field of Option)
%tag = extractvalue {i1, i64} %option, 0
switch i1 %tag, label %none [
  i1 true, label %some
]

some:
  %value = extractvalue {i1, i64} %option, 1
  br label %merge

none:
  br label %merge

merge:
  %result = phi i64 [ %value, %some ], [ 0, %none ]
  ret i64 %result
```

**Tasks:**
- [ ] Generate switch for enum tags
- [ ] Destructure struct/enum payloads
- [ ] Handle nested patterns
- [ ] Exhaustiveness already checked by type checker

**Acceptance Criteria:**
- Pattern matching compiles
- All patterns work (literals, structs, enums, wildcards)
- Generated code is efficient (no redundant checks)

---

## Week 7-8: Adaptive Functions (Issues #15-18)

### Issue #15: Generate solution functions
**Priority:** P0-critical
**Labels:** backend-llvm, adaptive

**Description:**
For each `@solution` in an adaptive function, generate a separate LLVM function.

**Example:**
```eclexia
adaptive def foo(n: Int) -> Int {
    @solution "a": { n * 2 }
    @solution "b": { n * n }
}
```

**Generated:**
```llvm
define i64 @foo_solution_a(i64 %n) { ... }
define i64 @foo_solution_b(i64 %n) { ... }
```

**Tasks:**
- [ ] Iterate over solutions in MIR
- [ ] Generate separate function for each
- [ ] Name functions `{parent}_solution_{name}`
- [ ] Ensure same signature as parent

**Acceptance Criteria:**
- Each solution compiles to a function
- Functions have correct signatures
- Can call solutions directly (for testing)

---

### Issue #16: Generate dispatch table
**Priority:** P0-critical
**Labels:** backend-llvm, adaptive

**Description:**
Create an array of function pointers for runtime dispatch.

**LLVM:**
```llvm
@foo_solutions = private constant [2 x ptr] [
  ptr @foo_solution_a,
  ptr @foo_solution_b
]
```

**Tasks:**
- [ ] Generate global constant array
- [ ] Store function pointers
- [ ] Index at runtime based on selection

**Acceptance Criteria:**
- Dispatch table exists in generated IR
- Can index and call correct function

---

### Issue #17: Generate shadow price selector call
**Priority:** P0-critical
**Labels:** backend-llvm, adaptive, runtime

**Description:**
Call runtime library to select optimal solution based on shadow prices.

**LLVM:**
```llvm
define i64 @foo(i64 %n) {
entry:
  %prices = call ptr @eclexia_runtime_get_shadow_prices()
  %solution_id = call i32 @eclexia_runtime_select_solution(
    ptr @foo_metadata,
    ptr %prices
  )
  ; ... dispatch based on %solution_id
}
```

**Tasks:**
- [ ] Define runtime function declarations
- [ ] Encode solution metadata (costs, conditions)
- [ ] Generate call to selector
- [ ] Handle selection result

**Acceptance Criteria:**
- Selector is called
- Returns solution index
- Metadata is accessible to runtime

---

### Issue #18: Implement adaptive function wrapper
**Priority:** P0-critical
**Labels:** backend-llvm, adaptive, milestone-3

**Description:**
Generate the full adaptive function wrapper that:
1. Calls shadow price scheduler
2. Dispatches to selected solution
3. Returns result

**Tasks:**
- [ ] Generate wrapper function
- [ ] Call scheduler
- [ ] Generate switch statement
- [ ] Handle all solutions
- [ ] Merge results with phi node

**Acceptance Criteria:**
- Adaptive fibonacci works
- Runtime selects correct solution
- Overhead < 50ns (measured)

---

## Week 9-10: Resource Tracking (Issues #19-23)

### Issue #19: Implement runtime resource tracker (Rust)
**Priority:** P0-critical
**Labels:** runtime

**Description:**
Implement the runtime library for resource tracking in Rust.

**Location:** `runtime/eclexia-runtime/src/tracking.rs`

**API:**
```rust
pub fn start_tracking() -> ResourceSnapshot;
pub fn stop_tracking(start: ResourceSnapshot) -> ResourceUsage;
pub fn current_energy() -> f64;  // Joules
pub fn current_carbon() -> f64;  // gCO2e
```

**Tasks:**
- [ ] Implement RAPL energy counters (Linux, Intel/AMD)
- [ ] Implement PowerMetrics (macOS, Apple Silicon)
- [ ] Implement timing (clock)
- [ ] Implement carbon calculation (energy × grid intensity)
- [ ] Add tests on multiple platforms

**Acceptance Criteria:**
- Works on Linux (Intel/AMD)
- Works on macOS (Apple Silicon)
- Returns accurate energy measurements (±10%)
- Documented limitations (e.g., doesn't work on Windows yet)

---

### Issue #20: Insert resource tracking hooks in LLVM IR
**Priority:** P1-high
**Labels:** backend-llvm, runtime

**Description:**
Insert calls to runtime tracking functions in generated code.

**Example:**
```eclexia
def foo(n: Int) -> Int
    @requires: energy < 100J
{
    n * 2
}
```

**Generated LLVM:**
```llvm
define i64 @foo(i64 %n) {
entry:
  %snapshot = call ptr @eclexia_runtime_start_tracking()
  %result = mul i64 %n, 2
  call void @eclexia_runtime_stop_tracking(ptr %snapshot)
  ret i64 %result
}
```

**Tasks:**
- [ ] Check if function has `@requires` annotation
- [ ] Insert start_tracking at function entry
- [ ] Insert stop_tracking before returns
- [ ] Handle multiple return paths

**Acceptance Criteria:**
- Tracking hooks inserted only when needed
- Works with multiple return statements
- Doesn't break control flow

---

### Issue #21: Implement zero-cost abstraction for tracking
**Priority:** P1-high
**Labels:** backend-llvm, performance

**Description:**
Ensure resource tracking has zero cost when unused.

**Strategy:**
- Functions without `@requires` → no tracking hooks
- LLVM dead-code elimination removes unused tracking
- Mark tracking functions as `alwaysinline`

**Tasks:**
- [ ] Only insert hooks when `@requires` present
- [ ] Mark runtime functions with LLVM attributes
- [ ] Run LLVM optimization passes (DCE, inline)
- [ ] Benchmark: functions without tracking should be identical to baseline

**Acceptance Criteria:**
- `def add(a: Int, b: Int)` compiles to single `add` instruction
- No tracking overhead when unused
- Benchmarks confirm zero cost

---

### Issue #22: Expose current_energy() and current_carbon() to user
**Priority:** P2-medium
**Labels:** backend-llvm, runtime

**Description:**
Allow user code to query current resource usage.

**Example:**
```eclexia
def main() -> Unit {
    do_work()
    println("Energy used: ", current_energy())
    println("Carbon emitted: ", current_carbon())
}
```

**Tasks:**
- [ ] Add `current_energy()` and `current_carbon()` to stdlib
- [ ] Generate calls to runtime library
- [ ] Return values as `Energy` and `Carbon` types

**Acceptance Criteria:**
- User can call these functions
- Returns accurate values
- Works with adaptive functions

---

### Issue #23: Benchmark resource tracking overhead
**Priority:** P1-high
**Labels:** runtime, performance, milestone-4

**Description:**
Measure overhead of resource tracking when enabled.

**Benchmarks:**
1. Function with tracking vs without
2. Adaptive function dispatch overhead
3. Energy measurement accuracy vs external tools

**Tasks:**
- [ ] Run benchmarks on multiple platforms
- [ ] Compare to Intel VTune, powermetrics
- [ ] Document overhead in `BENCHMARKS.md`
- [ ] Set acceptable overhead threshold (<50ns per call)

**Acceptance Criteria:**
- Overhead < 50ns per tracked function call
- Energy measurements within ±10% of external tools
- CI tracks performance regression

---

## Week 11-12: Optimization & Cross-Compilation (Issues #24-28)

### Issue #24: Implement LLVM optimization passes
**Priority:** P1-high
**Labels:** backend-llvm, performance

**Description:**
Run LLVM optimization passes on generated IR.

**Passes:**
- Constant folding
- Dead code elimination
- Function inlining
- Loop optimization
- SIMD vectorization

**Tasks:**
- [ ] Create optimization pipeline
- [ ] Add `-O0`, `-O1`, `-O2`, `-O3` flags
- [ ] Benchmark each optimization level
- [ ] Document trade-offs (compile time vs runtime)

**Acceptance Criteria:**
- `-O3` produces fast code (≤1.5x Rust)
- `-O0` compiles quickly (for dev builds)
- Benchmarks show clear improvement

---

### Issue #25: Implement cross-compilation support
**Priority:** P0-critical
**Labels:** backend-llvm, milestone-5

**Description:**
Support cross-compiling to multiple targets.

**Targets (MVP):**
- x86_64-unknown-linux-gnu
- aarch64-apple-darwin (M1/M2/M3)
- aarch64-unknown-linux-gnu (AWS Graviton)

**Tasks:**
- [ ] Add `--target` flag to CLI
- [ ] Set LLVM target triple
- [ ] Link against correct libc
- [ ] Test on all platforms (CI)

**Acceptance Criteria:**
- Can cross-compile from Linux → macOS ARM64
- Can cross-compile from macOS → Linux x86-64
- Binaries run on target platform

---

### Issue #26: Implement static linking
**Priority:** P1-high
**Labels:** backend-llvm

**Description:**
Produce statically linked binaries (single-file distribution).

**Tasks:**
- [ ] Link runtime library statically
- [ ] Link libc statically (musl on Linux)
- [ ] Minimize binary size (strip symbols)
- [ ] Test on systems without Eclexia installed

**Acceptance Criteria:**
- Binary runs without dependencies
- Size < 10MB for simple programs
- Works on minimal Linux (Alpine, busybox)

---

### Issue #27: Add Windows support
**Priority:** P2-medium
**Labels:** backend-llvm, windows

**Description:**
Support Windows as a target platform.

**Challenges:**
- Different calling conventions (stdcall vs sysv)
- MSVC toolchain vs MinGW
- Resource tracking (no RAPL on Windows)

**Tasks:**
- [ ] Set up Windows CI
- [ ] Test cross-compilation to `x86_64-pc-windows-msvc`
- [ ] Handle calling conventions
- [ ] Document resource tracking limitations

**Acceptance Criteria:**
- Compiles on Windows
- Binaries run on Windows
- Tests pass (except resource tracking)

---

### Issue #28: Create comprehensive test suite
**Priority:** P1-high
**Labels:** testing

**Description:**
Test suite covering all LLVM backend features.

**Test Categories:**
1. Type lowering (primitives, structs, functions)
2. Control flow (if, loops, recursion)
3. Adaptive functions (dispatch, selection)
4. Resource tracking (energy, carbon)
5. Cross-platform (Linux, macOS, Windows)

**Tasks:**
- [ ] Port all conformance tests to LLVM backend
- [ ] Add backend-specific tests
- [ ] Add cross-platform tests
- [ ] Run in CI on all platforms

**Acceptance Criteria:**
- All 32 conformance tests pass
- 100+ backend tests pass
- CI passes on Linux, macOS, Windows

---

## Bonus: Documentation & Polish (Issues #29-32)

### Issue #29: Write LLVM backend documentation
**Priority:** P2-medium
**Labels:** documentation

**Description:**
Document how the LLVM backend works for contributors.

**Sections:**
- Architecture overview
- Type lowering details
- Adaptive function codegen
- Resource tracking integration
- Debugging generated IR

**Location:** `docs/llvm-backend.md`

---

### Issue #30: Add llvm-dis integration for debugging
**Priority:** P2-medium
**Labels:** tooling

**Description:**
Allow developers to inspect generated LLVM IR.

**Command:**
```bash
eclexia build app.ecl --emit-llvm-ir
# Produces app.ll (human-readable LLVM IR)
```

**Tasks:**
- [ ] Add `--emit-llvm-ir` flag
- [ ] Save IR to file
- [ ] Pretty-print with syntax highlighting

---

### Issue #31: Profile-guided optimization (PGO)
**Priority:** P2-medium
**Labels:** performance, advanced

**Description:**
Use runtime profiles to guide LLVM optimization.

**Workflow:**
1. Compile with instrumentation
2. Run program, collect profile
3. Recompile with profile data
4. LLVM optimizes hot paths aggressively

---

### Issue #32: Link-time optimization (LTO)
**Priority:** P2-medium
**Labels:** performance, advanced

**Description:**
Enable LLVM's LTO for cross-module optimization.

**Benefits:**
- Inline across modules
- Dead code elimination across modules
- Smaller binaries
- Faster runtime

**Trade-off:** Longer compile times

---

## Meta: Project Management

### Weekly Check-ins
Post to GitHub Discussions every Friday:
- What was accomplished
- Blockers encountered
- Next week's focus
- Help needed

### Code Review
- All PRs require review
- Focus on correctness, not perfection
- Merge quickly, iterate fast

### Testing
- Write tests FIRST (TDD)
- Every feature needs tests
- CI must pass before merge

---

**TOTAL ISSUES: 32**
**TIMELINE: 12 weeks**
**OUTCOME: Production-ready LLVM backend** 🚀
