# Eclexia Self-Hosting & Universal Target Analysis

**Date:** 2026-02-07
**Goal:** Make Eclexia self-hosted, living by its own principles, targeting all major platforms

---

## Executive Summary

**Current Status:** Eclexia is 100% complete as a language but only has a **bytecode VM backend**. The compiler is ~10,000 lines of Rust across 63 files.

**Self-Hosting Feasibility:** **MODERATE** - Language is feature-complete, but needs:
1. FFI for calling C/system libraries
2. Unsafe operations for low-level code
3. Multiple backend implementations
4. Systems programming features

**Timeline Estimate:**
- **Phase 1** (Backend Development): 3-4 months
- **Phase 2** (Self-Hosting Bootstrap): 2-3 months
- **Phase 3** (Dogfooding & Polish): 1-2 months
- **Total:** 6-9 months to full self-hosting on all targets

---

## Current Architecture

### What Eclexia Has ✅

**Frontend (100% Complete):**
- ✅ Lexer (logos-based, Unicode support)
- ✅ Parser (hand-written recursive descent, 32/32 conformance tests)
- ✅ AST → HIR → MIR pipeline
- ✅ Type checker (Hindley-Milner with dimensional types)
- ✅ Resource tracking (energy, carbon, time, memory)
- ✅ Adaptive functions with `@solution` blocks
- ✅ Pattern matching, closures, generics, Option types

**Backend (Partial):**
- ✅ Bytecode VM (fully functional, debugger included)
- ⚠️ Cranelift JIT (stub only - "not yet implemented")
- ❌ LLVM backend (mentioned in docs, not implemented)
- ❌ WebAssembly backend (mentioned in docs, not implemented)
- ❌ Native code generation (no x86/ARM/RISC-V codegen)

**Tooling (100% Complete):**
- ✅ REPL
- ✅ LSP server (3.0MB binary)
- ✅ Formatter
- ✅ Linter
- ✅ CLI with 12 commands

### What Eclexia Lacks for Self-Hosting ❌

**Critical Gaps:**

1. **No FFI (Foreign Function Interface)**
   - Cannot call C libraries (libc, LLVM C API, etc.)
   - Cannot interface with operating system
   - Cannot use existing libraries

2. **No Unsafe/Raw Operations**
   - Cannot manipulate raw pointers
   - Cannot do manual memory management
   - Cannot implement low-level data structures

3. **No Native Code Generation**
   - Only bytecode VM exists
   - No way to compile to machine code
   - No optimization for production workloads

4. **No Multiple Backend Support**
   - LLVM stub doesn't exist
   - Cranelift stub is empty
   - WASM backend not started
   - No RISC-V target

5. **Missing Systems Programming Features**
   - No inline assembly
   - No memory layout control (`#[repr(C)]`)
   - No zero-cost abstractions guarantee
   - No compile-time evaluation (const fn)

---

## Target Platform Requirements

### Strategic Vision

> "Get to every platform so there's no excuse anywhere not to be using it"

**Required Targets:**

| Target | Priority | Rationale |
|--------|----------|-----------|
| **LLVM** | CRITICAL | Universal backend, enables all native platforms |
| **WebAssembly** | CRITICAL | Browser, WASI, edge computing, universal runtime |
| **x86-64** | HIGH | Desktop/server dominance |
| **ARM64** | HIGH | Mobile, Apple Silicon, embedded |
| **RISC-V** | HIGH | Open ISA, future-proof, embedded |
| **Native (Cranelift)** | MEDIUM | Fast compilation for dev builds |
| **Embedded** | MEDIUM | IoT, resource-constrained devices |

### Backend Implementation Strategy

```
┌─────────────────────────────────────────────────────────────────┐
│                        Eclexia MIR                              │
│        (Already exists, resource-aware, adaptive)               │
└─────────────┬───────────────────────────────────────────────────┘
              │
              ├─────────────┬─────────────┬──────────────┬─────────┐
              │             │             │              │         │
              ▼             ▼             ▼              ▼         ▼
       ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌────────┐
       │  LLVM IR │  │   WASM   │  │Cranelift │  │ Bytecode │  │ Custom │
       │          │  │          │  │   (JIT)  │  │   (VM)   │  │ Native │
       └─────┬────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘  └───┬────┘
             │            │             │              │            │
    ┌────────┴────────┐   │             │              │            │
    ▼        ▼        ▼   ▼             ▼              ▼            ▼
  x86-64  ARM64  RISC-V  Browser      Fast         Portable    Embedded
                         /WASI        Dev          Reference
```

---

## Self-Hosting Roadmap

### Phase 1: Backend Development (3-4 months)

**Goal:** Implement backends needed to compile Eclexia to native code

#### Step 1.1: LLVM Backend (8-10 weeks)
**Status:** Not started
**Lines of Code:** ~5,000-8,000 estimated

**Tasks:**
- [ ] Integrate `llvm-sys` or `inkwell` (Rust LLVM bindings)
- [ ] Implement MIR → LLVM IR lowering
- [ ] Map Eclexia types to LLVM types
- [ ] Implement resource tracking instrumentation in LLVM IR
- [ ] Implement adaptive function dispatch (function pointers + runtime selection)
- [ ] Shadow price hook integration (call runtime library)
- [ ] Support all LLVM targets (x86-64, ARM64, RISC-V, etc.)

**Key Challenges:**
- Resource tracking must generate efficient instrumentation code
- Adaptive functions need runtime scheduling (call out to runtime library)
- Dimensional types must compile down to primitives

**Example MIR → LLVM:**
```rust
// Eclexia MIR
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "efficient": /* ... */
    @solution "naive": /* ... */
}

// LLVM IR (conceptual)
define i64 @fibonacci(i64 %n) {
  ; Check resource constraints
  call void @record_energy_start()

  ; Call runtime scheduler to select solution
  %solution_id = call i32 @select_adaptive_solution(
    @fibonacci_solutions, ; metadata
    %n                    ; runtime context
  )

  ; Dispatch to selected solution
  switch i32 %solution_id, label %default [
    i32 0, label %efficient
    i32 1, label %naive
  ]

efficient:
  %result_efficient = call i64 @fibonacci_efficient(i64 %n)
  br label %done

naive:
  %result_naive = call i64 @fibonacci_naive(i64 %n)
  br label %done

done:
  %result = phi i64 [ %result_efficient, %efficient ], [ %result_naive, %naive ]
  call void @record_energy_end()
  ret i64 %result
}
```

#### Step 1.2: WebAssembly Backend (4-6 weeks)
**Status:** Not started
**Lines of Code:** ~3,000-5,000 estimated

**Approach:** Two options:
1. **Via LLVM:** LLVM can already target WASM → easiest path
2. **Direct WASM codegen:** More control, smaller binary

**Tasks:**
- [ ] Choose approach (recommend LLVM → WASM32 target)
- [ ] OR: Implement direct MIR → WASM lowering using `walrus` or `wasm-encoder`
- [ ] WASI integration for system calls
- [ ] Browser compatibility (no threading initially)
- [ ] Resource tracking using WASM linear memory

#### Step 1.3: Cranelift Backend (3-4 weeks)
**Status:** Stub exists, not implemented
**Lines of Code:** ~2,000-3,000 estimated

**Use Case:** Fast compilation for development builds (not production)

**Tasks:**
- [ ] Integrate `cranelift-codegen` and `cranelift-module`
- [ ] Implement MIR → Cranelift IR lowering
- [ ] JIT execution support
- [ ] Fast-path for REPL and testing

---

### Phase 2: Self-Hosting Bootstrap (2-3 months)

**Goal:** Rewrite the Eclexia compiler in Eclexia itself

#### Step 2.1: Add Systems Programming Features (4-6 weeks)

**Missing Language Features:**

1. **FFI Support**
   ```eclexia
   // Need syntax for external functions
   extern "C" def malloc(size: usize) -> *mut u8

   // Call C libraries
   extern "C" def LLVMCreateBuilder() -> LLVMBuilderRef
   ```

2. **Unsafe/Raw Operations**
   ```eclexia
   // Pointer manipulation
   unsafe def ptr_offset(ptr: *mut T, offset: isize) -> *mut T

   // Manual memory management
   unsafe def write_bytes(ptr: *mut u8, val: u8, count: usize) -> Unit
   ```

3. **Memory Layout Control**
   ```eclexia
   // C-compatible struct layout
   @repr(C)
   struct LLVMOpaqueValue {
       // ...
   }
   ```

4. **Compile-Time Evaluation**
   ```eclexia
   // Const functions for metaprogramming
   const def size_of<T>() -> usize
   ```

**Implementation:**
- Extend parser for `extern`, `unsafe`, `@repr` annotations
- Add unsafe operations to HIR/MIR
- Implement pointer arithmetic in codegen
- Add compile-time evaluator

#### Step 2.2: Port Compiler Components (8-12 weeks)

**Strategy:** Incremental port, one module at a time

**Module-by-Module Plan:**

| Module | Rust LOC | Eclexia LOC Est. | Difficulty | Order |
|--------|----------|------------------|------------|-------|
| AST definitions | ~1,000 | ~800 | Easy | 1 |
| Lexer | ~1,500 | ~1,200 | Medium | 2 |
| Parser | ~2,500 | ~2,000 | Hard | 3 |
| Type checker | ~2,000 | ~1,600 | Hard | 4 |
| HIR lowering | ~1,000 | ~800 | Medium | 5 |
| MIR lowering | ~1,500 | ~1,200 | Medium | 6 |
| Optimizations | ~500 | ~400 | Easy | 7 |
| LLVM backend | ~5,000 | ~4,000 | Very Hard | 8 |
| Runtime | ~2,000 | ~1,600 | Hard | 9 |
| CLI/Driver | ~1,000 | ~800 | Easy | 10 |
| **TOTAL** | **~18,000** | **~14,400** | | |

**Bootstrap Process:**
1. Port AST/data structures first (pure data, easy)
2. Port lexer/parser (no external deps)
3. Port type checker (uses data structures)
4. Port HIR/MIR lowering
5. **Critical transition:** Port LLVM backend to Eclexia
6. At this point, Eclexia can compile itself!
7. Port remaining components (runtime, CLI)

**Chicken-and-Egg Solution:**
```bash
# Stage 0: Rust compiler (original)
eclexia-rs/         # Current Rust implementation

# Stage 1: Eclexia compiler in Eclexia, compiled by Rust
eclexia-ecl/        # Eclexia source code
eclexia-rs eclexia-ecl/ -o eclexia-stage1

# Stage 2: Self-compiled Eclexia compiler
eclexia-stage1 eclexia-ecl/ -o eclexia-stage2

# Verify: Stage 2 should produce identical output
eclexia-stage2 eclexia-ecl/ -o eclexia-stage3
diff eclexia-stage2 eclexia-stage3  # Should be identical (reproducible builds)
```

---

### Phase 3: Dogfooding & Ecosystem (1-2 months)

**Goal:** Use Eclexia for real projects, validate self-hosting works

#### Step 3.1: Rewrite Key Tools in Eclexia

**Candidates:**
- [ ] CLI tools (formatter, linter) → rewrite in Eclexia
- [ ] LSP server → rewrite in Eclexia (currently Rust)
- [ ] Build system → Eclexia-native build tool
- [ ] Package manager → Eclexia-based registry client

#### Step 3.2: Demonstrate Living by Principles

**The compiler should use adaptive functions for:**

1. **Parsing Strategy Selection**
   ```eclexia
   adaptive def parse_file(source: String) -> AST
       @requires: latency < 500ms, energy < 50J
       @optimize: minimize latency
   {
       @solution "incremental":
           @when: file_size < 100KB && cached
           @provides: latency: 50ms, energy: 5J
       { /* incremental parse */ }

       @solution "full_parse":
           @when: true
           @provides: latency: 300ms, energy: 30J
       { /* full parse from scratch */ }
   }
   ```

2. **Optimization Level Selection**
   ```eclexia
   adaptive def optimize(mir: MIR) -> MIR
       @requires: energy < 200J
       @optimize: minimize compile_time, maximize runtime_perf
   {
       @solution "o0": /* no optimization */
       @solution "o1": /* basic optimization */
       @solution "o2": /* moderate optimization */
       @solution "o3": /* aggressive optimization */
   }
   ```

3. **Backend Selection at Runtime**
   ```eclexia
   adaptive def codegen(mir: MIR) -> Object
       @requires: energy < 500J
       @optimize: minimize compile_time
   {
       @solution "cranelift":
           @when: dev_build && fast_compile_needed
           @provides: compile_time: 100ms, energy: 50J
       { /* JIT with Cranelift */ }

       @solution "llvm_fast":
           @when: !dev_build
           @provides: compile_time: 500ms, energy: 200J
       { /* LLVM -O1 */ }

       @solution "llvm_optimized":
           @when: release_build
           @provides: compile_time: 2000ms, energy: 800J
       { /* LLVM -O3 */ }
   }
   ```

**This demonstrates:** The compiler *uses* Economics-as-Code to optimize itself!

---

## Universal Platform Deployment

### Target Matrix

| Platform | Backend | Status | Priority | Use Case |
|----------|---------|--------|----------|----------|
| **Linux x86-64** | LLVM | TODO | CRITICAL | Server, desktop |
| **Linux ARM64** | LLVM | TODO | CRITICAL | Cloud, mobile |
| **Linux RISC-V** | LLVM | TODO | HIGH | Future-proof, open hardware |
| **macOS ARM64** | LLVM | TODO | HIGH | Apple Silicon |
| **macOS x86-64** | LLVM | TODO | MEDIUM | Intel Macs |
| **Windows x86-64** | LLVM | TODO | HIGH | Desktop, gaming |
| **Browser (WASM)** | WASM | TODO | CRITICAL | Web apps, playground |
| **WASI** | WASM | TODO | HIGH | Portable CLI tools |
| **Embedded ARM** | LLVM | TODO | MEDIUM | IoT, edge devices |
| **Bare metal** | Custom | TODO | LOW | OS development |

### Distribution Strategy

**Goal:** "No excuse not to use Eclexia anywhere"

**Approaches:**

1. **Single Binary Distribution**
   - Static linking (no dependencies)
   - Cross-compile from any host to any target
   - Guix/Nix packages for reproducibility

2. **WASM Universal Runtime**
   - `eclexia.wasm` runs anywhere WASI is supported
   - Browser-based playground (no install needed)
   - Edge computing (Cloudflare Workers, Fastly Compute@Edge)

3. **Package Manager Integration**
   - Guix package: `guix install eclexia`
   - Nix package: `nix-env -i eclexia`
   - Homebrew: `brew install eclexia`
   - Cargo: `cargo install eclexia-lang`
   - npm (wrapper): `npx eclexia` (calls WASM binary)

4. **CI/CD Integration**
   - GitHub Actions: `uses: eclexia-lang/setup-eclexia@v1`
   - GitLab CI: `image: eclexia/builder:latest`
   - Pre-built binaries for all CI platforms

---

## Technical Challenges & Solutions

### Challenge 1: Resource Tracking Overhead

**Problem:** Instrumenting every function with energy/carbon tracking adds overhead

**Solution:**
1. **Zero-cost abstractions:** Resource tracking is compile-time when constraints are static
2. **Lazy tracking:** Only track resources when `@requires` is present
3. **Sampling:** Don't track every operation, use statistical sampling
4. **LLVM optimization:** Let LLVM dead-code-eliminate unused tracking

**Example:**
```eclexia
// No @requires → no tracking overhead (zero cost)
def add(a: Int, b: Int) -> Int {
    a + b
}

// Has @requires → runtime tracking inserted
def expensive_op(data: Data) -> Result
    @requires: energy < 1000J
{
    // Tracking code injected by compiler
}
```

### Challenge 2: Adaptive Function Runtime

**Problem:** Runtime must select optimal solution based on shadow prices

**Solution:**
1. **Precompile all solutions:** Each `@solution` is a separate function
2. **Lightweight scheduler:** Simple linear program solver (good_lp crate)
3. **Cache decisions:** Memoize solution selection based on context
4. **Fallback:** Always have a default solution that meets constraints

**Implementation:**
```rust
// Generated code (conceptual)
fn fibonacci_adaptive(n: i64) -> i64 {
    let solutions = [
        Solution { cost: [5, 10, 1], func: fibonacci_efficient },
        Solution { cost: [50, 50, 5], func: fibonacci_naive },
    ];

    let shadow_prices = runtime::get_shadow_prices();
    let selected = runtime::select_solution(&solutions, &shadow_prices);

    selected.func(n)
}
```

### Challenge 3: Cross-Platform Compilation

**Problem:** Compiling from any host to any target

**Solution:**
- **LLVM handles this:** `rustc --target` model
- Ship LLVM prebuilt for common hosts
- Cross-compile LLVM if needed (Guix/Nix do this)
- WASM backend is automatically portable

**Command:**
```bash
eclexia build --target x86_64-unknown-linux-gnu
eclexia build --target aarch64-apple-darwin
eclexia build --target wasm32-wasi
eclexia build --target riscv64gc-unknown-linux-gnu
```

---

## Resource Requirements

### Development Team

| Role | Time | Justification |
|------|------|---------------|
| **Compiler Engineer** | 6-9 months FTE | LLVM backend, self-hosting |
| **Systems Programmer** | 3-4 months FTE | FFI, unsafe, low-level features |
| **PL Researcher** | 2-3 months FTE | Formal verification, type system |
| **DevOps Engineer** | 1-2 months FTE | CI/CD, cross-compilation, packaging |

**Total Effort:** ~12-18 person-months

### Infrastructure

- **CI/CD:** GitHub Actions (free for open source)
- **Cross-compilation:** Guix build farm or self-hosted runners
- **Testing:** Physical hardware for ARM64, RISC-V (can use QEMU initially)
- **Hosting:** Static site for docs, package registry (Cloudflare Pages free tier)

---

## Success Metrics

### Self-Hosting
- [ ] Eclexia compiler written 100% in Eclexia
- [ ] Stage 2 = Stage 3 (reproducible builds)
- [ ] Compile time ≤ 2x Rust version
- [ ] Binary size ≤ 1.5x Rust version

### Universal Deployment
- [ ] Supports 8+ target platforms
- [ ] Single binary <20MB (statically linked)
- [ ] WASM binary <5MB
- [ ] Available in 3+ package managers

### Dogfooding
- [ ] Compiler uses adaptive functions for optimization selection
- [ ] Compiler tracks and reports its own resource usage
- [ ] Standard library written in Eclexia (not Rust)
- [ ] All tooling (LSP, formatter, linter) in Eclexia

### Ecosystem
- [ ] 10+ packages in registry
- [ ] 100+ GitHub stars
- [ ] Documentation site with interactive playground
- [ ] At least one real-world production user

---

## Recommended Next Steps

### Immediate (This Week)
1. **Validate LLVM approach:** Write a minimal MIR → LLVM IR prototype
2. **FFI design:** Draft syntax and semantics for `extern` functions
3. **Create issues:** Break down Phase 1 into GitHub issues

### Short-term (This Month)
4. **Start LLVM backend:** Begin implementation (~8-10 weeks)
5. **Add FFI support:** Parser changes, HIR/MIR support
6. **Benchmark bytecode VM:** Establish baseline performance

### Medium-term (Next 3 Months)
7. **Complete LLVM backend:** Full MIR → LLVM lowering
8. **WASM backend:** Via LLVM or direct codegen
9. **Port first module:** Rewrite AST definitions in Eclexia

### Long-term (6-9 Months)
10. **Complete self-hosting bootstrap:** All compiler code in Eclexia
11. **Multi-target release:** Binaries for Linux, macOS, Windows, WASM
12. **Public announcement:** Blog post, HN/Reddit launch

---

## Conclusion

**Self-hosting Eclexia is ACHIEVABLE in 6-9 months.**

**Key Insight:** The language is feature-complete, but the **backend is 80% missing**. Once LLVM backend exists, self-hosting becomes straightforward incremental porting.

**Strategic Advantage:** A self-hosted Eclexia compiler that **uses its own principles** (adaptive functions, resource tracking) is a powerful demonstration of Economics-as-Code in practice.

**Universal Deployment:** LLVM + WASM gives you every major platform. RISC-V support ensures future-proofing. No excuses.

**The Mission:** Once Eclexia self-hosts and hits M1, Snapdragon, GPUs, RISC-V, and WASM—when it's running EVERYWHERE—it becomes impossible to dismiss. The compiler itself uses adaptive functions to optimize its own compilation. This is the profound statement: **Economics-as-Code isn't theory, it's production.**

**Next Action:** Start the LLVM backend. Everything else follows from that.
