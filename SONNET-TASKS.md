# SONNET-TASKS.md -- Eclexia Completion Tasks

> **Generated:** 2026-02-12 by Opus 4.6 audit
> **Purpose:** Unambiguous instructions for Sonnet to complete all stubs, TODOs, and placeholder code.
> **Honest completion before this file:** ~60% (docs claim higher -- some inflated)
>
> **Prior audit (2026-02-09) claimed ~45% -- this was too pessimistic. The runtime stubs (scheduler.rs,
> profiler.rs, carbon.rs, shadow.rs) are NO LONGER 6-line TODOs; they have real implementations with
> tests. Shadow prices are NOT hardcoded 1.0/1.0/1.0 -- they use real defaults (energy=0.000033,
> time=0.001, memory=0.0000001, carbon=0.00005). The bytes CVE has been fixed (now 1.11.1).
> However, multiple real gaps remain as documented below.**

---

## GROUND RULES FOR SONNET

1. Read this entire file before starting any task.
2. Do tasks in order listed. Earlier tasks unblock later ones.
3. After each task, run the verification command. If it fails, fix before moving on.
4. Do NOT mark done unless verification passes.
5. Update `.machine_readable/STATE.scm` with honest completion percentages after each task.
6. Commit after each task: `fix(component): complete <description>`
7. Run `cargo test --workspace --lib` after every 3 tasks.
8. Run `cargo clippy --workspace` to check for warnings.

---

## TASK 1: Wire concurrency expressions through HIR lowering (HIGH)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-hir/src/lower.rs` (lines 1058-1083)

**Problem:** All concurrency-related AST expressions (`Spawn`, `Channel`, `Send`, `Recv`, `Select`, `YieldExpr`) and `MacroCall` are lowered to `ExprKind::Literal(Literal::Unit)` in HIR. This means the compiler silently discards these constructs in the bytecode/codegen path. There are NOTE comments on lines 1066, 1070, 1075, 1079, and 1082 marking each as pending.

**What to do:**

1. Add new `ExprKind` variants in `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-hir/src/lib.rs` for concurrency:
   - `Spawn { body: ExprId }`
   - `Channel { elem_ty: Option<TypeId>, capacity: Option<ExprId> }`
   - `Send { channel: ExprId, value: ExprId }`
   - `Recv { channel: ExprId }`
   - `Select { arms: Vec<SelectArm> }` (define `SelectArm` struct)
   - `Yield { value: Option<ExprId> }`
   - `MacroCall { name: SmolStr, args: Vec<ExprId> }`
2. Update `lower_expr` in `lower.rs` (lines 1058-1083) to actually lower each AST concurrency expression into its corresponding HIR variant instead of `Literal(Unit)`.
3. Update the HIR pretty printer in `eclexia-fmt` if it pattern-matches on `ExprKind` exhaustively.
4. Update any exhaustive matches on `ExprKind` in `eclexia-mir/src/lower.rs` -- for now, MIR lowering can emit a `Nop` or a `Call` to a runtime intrinsic for each concurrency variant.

**Verification:**
```bash
cargo build --workspace 2>&1 | head -50
cargo test --workspace --lib 2>&1 | tail -20
```

---

## TASK 2: Implement concurrency expressions in the interpreter (HIGH)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-interp/src/eval.rs` (lines 689-707)

**Problem:** All six concurrency expressions (`Spawn`, `Channel`, `Send`, `Recv`, `Select`, `YieldExpr`) return `RuntimeError::custom("... not yet supported in interpreter")`. The `eclexia-async` crate already has a working async runtime with channels, tasks, and parallel iterators (162 lines, 10 tests). These need to be connected.

**What to do:**

1. Add a `tokio::runtime::Runtime` handle (or the `eclexia_async::Runtime`) to the interpreter's `Interpreter` struct. Initialize it lazily on first concurrency expression.
2. For `Spawn`: wrap the inner expression evaluation in a spawned tokio task. Return a `Value::TaskHandle(...)` variant (add to `value.rs`).
3. For `Channel`: create an `mpsc` channel from `eclexia_async`, return a `Value::Tuple` of `(Sender, Receiver)` wrapped in new Value variants.
4. For `Send`: extract the channel sender from the value, call `.send()`.
5. For `Recv`: extract the channel receiver, call `.recv()`.
6. For `Select`: implement using `tokio::select!` or a polling loop over multiple receivers.
7. For `YieldExpr`: call `tokio::task::yield_now()`.
8. Add the new `Value` variants (`TaskHandle`, `Sender`, `Receiver`) to `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-interp/src/value.rs`.
9. Add at least 3 tests: spawn+join, channel send/recv, yield.

**Verification:**
```bash
cargo test -p eclexia-interp --lib 2>&1 | tail -20
# Create a test file:
# test_spawn.ecl: let h = spawn(|| 42); await(h)
# cargo run -- run test_spawn.ecl
```

---

## TASK 3: Complete Coq proof admits in Typing.v (MEDIUM)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/formal/coq/src/Typing.v` (lines 317, 383, 391, 396, 461)

**Problem:** Three theorems have `Admitted` in Typing.v:
- `weakening` (line 317): one admit remains for the variable case weakening lemma.
- `progress` (line 396): two admits at lines 383 and 391 -- need step rules for boolean operations (`STBinOpBool`) and comparison operations (`STBinOpCmp`).
- `preservation` (line 461): one admit for comparison step rule interaction.

Total: 3 theorems with 4 `Admitted` uses.

**What to do:**

1. Define step rules `STBinOpBool` for boolean binary operations (and, or) in the `step` inductive relation. Pattern: both operands are `VBool` values, produce a `VBool` result.
2. Define step rules `STBinOpCmp` for comparison operations (eq, ne, lt, le, gt, ge). Pattern: both operands are `VInt` values, produce a `VBool` result.
3. Prove the variable case in `weakening` using a lookup lemma on context extension.
4. Replace all `Admitted` with actual proof terms using the new step rules.
5. Ensure `coqc` compiles all three files without errors.

**Verification:**
```bash
cd /var/mnt/eclipse/repos/eclexia/formal/coq
coqc -R src Eclexia src/Syntax.v src/Typing.v src/ShadowPrices.v 2>&1
# Should report 0 errors. All Admitted should be gone from Typing.v.
grep -c "Admitted" src/Typing.v
# Expected output: 0
```

---

## TASK 4: Complete Coq proof admits in ShadowPrices.v (MEDIUM)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/formal/coq/src/ShadowPrices.v` (lines 163, 190, 212, 232, 332)

**Problem:** Five theorems have `Admitted`:
- `strong_duality` (line 163): requires Farkas' lemma.
- `dual_variables_are_shadow_prices` (line 190): requires LP sensitivity analysis.
- `slack_implies_zero_shadow_price` (line 212): requires complementary slackness.
- `positive_shadow_price_implies_binding` (line 232): contrapositive of the above.
- `monotonicity` (line 332): nearly complete, monotonicity in 4 regions established.

Total: 5 `Admitted` uses.

**What to do:**

1. For `strong_duality`: This is a deep LP theory result. Two options:
   a. Implement a proof using Farkas' lemma (hard but complete).
   b. Convert to an axiom with `Axiom` and document why (pragmatic).
2. For `dual_variables_are_shadow_prices`: Prove using `strong_duality` as a lemma. The key insight is that perturbing constraint `i` by epsilon changes the optimal value by `lambda_i * epsilon`.
3. For `slack_implies_zero_shadow_price`: Prove by contradiction using complementary slackness: if the constraint is slack and the dual variable is positive, the KKT product `lambda * slack > 0`, contradicting the KKT condition `lambda * slack = 0`.
4. For `positive_shadow_price_implies_binding`: Prove as contrapositive of `slack_implies_zero_shadow_price`. If the constraint is not binding (i.e., slack), then the shadow price is zero, contradicting the hypothesis that it is positive.
5. For `monotonicity`: Complete the remaining cases. The proof structure already handles 4 regions -- finish the boundary cases.

**Verification:**
```bash
cd /var/mnt/eclipse/repos/eclexia/formal/coq
coqc -R src Eclexia src/Syntax.v src/ShadowPrices.v 2>&1
grep -c "Admitted" src/ShadowPrices.v
# Expected output: 0 (or 1 if strong_duality is made an Axiom)
```

---

## TASK 5: Remove old cranelift_backend.rs placeholder stub (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-codegen/src/cranelift_backend.rs` (44 lines)

**Problem:** This file contains an empty placeholder `CraneliftBackend` struct that always returns `Err(CodegenError::UnsupportedFeature(...))`. The real Cranelift backend lives in the separate `eclexia-cranelift` crate (`compiler/eclexia-cranelift/src/lib.rs`, 1937 lines) and works correctly. The stub in `eclexia-codegen` shadows the real one and may confuse users of the codegen crate.

**What to do:**

1. Check if anything in the workspace imports `eclexia_codegen::CraneliftBackend` (the stub version). Search for `use eclexia_codegen::CraneliftBackend`.
2. If nothing uses it, remove the file `cranelift_backend.rs` and remove `mod cranelift_backend;` and `pub use cranelift_backend::CraneliftBackend;` from `eclexia-codegen/src/lib.rs`.
3. If something does use it, redirect it to `eclexia_cranelift::CraneliftBackend` instead.
4. Ensure `cargo build --workspace` still compiles.

**Verification:**
```bash
cargo build --workspace 2>&1 | tail -5
cargo test --workspace --lib 2>&1 | tail -5
grep -r "eclexia_codegen::CraneliftBackend" /var/mnt/eclipse/repos/eclexia/compiler/ --include="*.rs"
# Expected: no results (nobody should be using the stub anymore)
```

---

## TASK 6: Wire remaining reactive crates into CLI (MEDIUM)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia/src/commands.rs`

**Problem:** The ROADMAP.adoc (line 58) and QUICK_STATUS.md (line 73) state that 4 of 7 reactive crates are wired into `build --analyze`: absinterp, comptime, specialize, effects. The remaining 3 -- `eclexia-db`, `eclexia-modules`, `eclexia-tiered` -- are partially wired. Specifically:
- `eclexia-db` is used in `build --analyze` for salsa-based incremental checking (line 869 of commands.rs), but only for a single file -- multi-file incremental builds do not use it.
- `eclexia-modules` is used for multi-file builds with dependency resolution and parallel compilation (line 247+), but the module system does not participate in `--analyze`.
- `eclexia-tiered` has a TierManager created (line 822) but the tiered execution path only shows tier recommendations -- it does not actually dispatch to different tiers.

**What to do:**

1. In the `build --analyze` path, after the existing absinterp/comptime/specialize/effects analyses, add:
   a. Module-level analysis: run `eclexia_modules::extract_imports` on all files in the project and report import graph statistics (number of modules, dependency depth, potential cycles).
   b. Tiered recommendation: use the `TierManager` to suggest which tier each function should run at based on its complexity and resource profile.
2. In the multi-file build path, use `eclexia-db` for incremental compilation by storing each file's `SourceFile` in the salsa database and querying `all_diagnostics` through salsa instead of ad-hoc parsing.
3. Add a `--watch` flag to `build` that uses `eclexia-tiered`'s watch mode (`eclexia_tiered::watch`) to re-trigger builds on file changes.

**Verification:**
```bash
cargo build --workspace 2>&1 | tail -5
# Test analyze with a multi-file project:
mkdir -p /tmp/eclexia-test-project/src
echo 'def main() -> Unit { println("hello") }' > /tmp/eclexia-test-project/src/main.ecl
cargo run -- build --analyze /tmp/eclexia-test-project/src/main.ecl 2>&1
# Should show module analysis and tier recommendations in addition to existing output
```

---

## TASK 7: Implement concurrency builtins in bytecode VM (MEDIUM)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-codegen/src/bytecode.rs`
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-codegen/src/vm.rs`

**Problem:** The stdlib `async.ecl` declares concurrency builtins (`task_spawn`, `task_await`, `task_yield`, `task_sleep`, `channel_create`, `channel_send`, `channel_recv`, `channel_try_recv`, `channel_select`, `parallel_all`, `parallel_race`) but the bytecode VM does not implement any of them. When `CallBuiltin` encounters these names, they are not dispatched.

**What to do:**

1. In `vm.rs`, in the `CallBuiltin` dispatch section, add cases for each concurrency builtin:
   - `task_spawn`: Create a new thread/tokio task, push a handle value onto the stack.
   - `task_await`: Pop the handle, join the task, push the result.
   - `task_yield`: Call `std::thread::yield_now()`.
   - `task_sleep`: Pop millis, sleep.
   - `channel_create`: Create an `mpsc` channel, push (sender, receiver) tuple.
   - `channel_send`: Pop value and sender, send.
   - `channel_recv`: Pop receiver, recv, push result.
   - `channel_try_recv`: Pop receiver, try_recv, push Option.
   - `channel_select`, `parallel_all`, `parallel_race`: Implement using tokio or rayon.
2. Add the `tokio` dependency to `eclexia-codegen/Cargo.toml` if not already present, or use `std::sync::mpsc` for a simpler initial implementation.
3. Add at least 3 VM-level tests for spawn/await, channel send/recv, and sleep.

**Verification:**
```bash
cargo test -p eclexia-codegen --lib 2>&1 | tail -20
cargo run -- build examples/fibonacci_adaptive.ecl 2>&1 | tail -5
```

---

## TASK 8: Add real memory tracking to profiler (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/runtime/eclexia-runtime/src/profiler.rs` (line 128)

**Problem:** The profiler's `end_span` method on line 128 sets `memory_bytes: 0.0` with the comment "memory tracking requires OS integration". Energy and carbon are estimated from wall-clock time, but memory is always zero. The `SpanAggregate` also never accumulates memory (`total_memory_bytes` is always 0.0).

**What to do:**

1. On Linux, read `/proc/self/statm` or `/proc/self/status` to get RSS (Resident Set Size) before and after a span. The delta is the memory consumed by the span.
2. Add a `memory_before` field to `ActiveSpan` that captures RSS at `begin_span`.
3. In `end_span`, capture RSS again and compute the delta.
4. Fall back to 0.0 on non-Linux platforms (wrap in `#[cfg(target_os = "linux")]`).
5. Update the test `test_begin_end_span` to verify `memory_bytes >= 0.0` (it will be non-negative but may be zero on CI).

**Verification:**
```bash
cargo test -p eclexia-runtime --lib profiler 2>&1
# Check that memory tracking works:
cargo test -p eclexia-runtime --lib test_begin_end_span 2>&1
```

---

## TASK 9: Implement Cranelift string data sections (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-cranelift/src/lib.rs` (lines 636-638)

**Problem:** String constants in the Cranelift backend are lowered to `iconst(I64, 0)` (a null pointer placeholder). The comment on line 637 says "Placeholder: real string data needs module-level data sections." This means any Eclexia program using string literals cannot produce correct native code through Cranelift.

**What to do:**

1. Add a data section to the `NativeModule` output that stores string constant bytes.
2. In `lower_value_cranelift` for `ConstantKind::String(s)`:
   a. Record the string bytes in a module-level data structure (e.g., `Vec<(SmolStr, Vec<u8>)>` in a `DataSection` struct).
   b. Emit a `global_value` or `symbol_value` instruction that refers to the string's offset in the data section.
   c. Return the pointer to the string data.
3. Similar treatment for `ConstantKind::Function` with unknown names (line 644) -- these should be proper relocations, not null pointers.
4. Add a test `test_cranelift_string_data_section` that verifies a function returning a string constant produces real codegen with code_size > 0 and a non-null pointer.

**Verification:**
```bash
cargo test -p eclexia-cranelift --lib 2>&1 | tail -20
```

---

## TASK 10: Implement Range/RangeInclusive in Cranelift backend (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-cranelift/src/lib.rs` (lines 853-854, 913-914)

**Problem:** Both integer and float binary operations for `Range` and `RangeInclusive` emit `iconst(I64, 0)` -- a placeholder zero value. The comments say "range values need runtime support." This means `for i in 0..10` compiles to nothing useful in Cranelift.

**What to do:**

1. Decide on a range representation: a 2-element struct `{start: i64, end: i64}` (or `{start, end, inclusive: bool}`). Use a stack-allocated pair.
2. For `BinaryOp::Range`: create a pair `(lhs, rhs)` stored in two local slots. Return a pointer to the pair.
3. For `BinaryOp::RangeInclusive`: same but with a flag or by adding 1 to the end.
4. Alternatively, if the range is only used in `for` loops, lower the range directly to a loop counter initialization in the MIR lowering pass and skip materializing the range as a value.
5. Add tests for both `Range` and `RangeInclusive` code generation.

**Verification:**
```bash
cargo test -p eclexia-cranelift --lib 2>&1 | tail -20
```

---

## TASK 11: Remove unwrap() calls in production code paths (MEDIUM)

**Files:** Multiple files across the compiler (73 total unwrap/panic occurrences in compiler/).

**Problem:** The panic-attack scan from 2026-02-09 found 327 unwraps, 28 unsafe blocks, and 48 panic sites across 47,295 lines. While most unwraps are in test code (e.g., `builtins.rs` has 96 in tests), some are in production paths:
- `compiler/eclexia-parser/src/lib.rs`: 1 unwrap (was 84, most fixed)
- `compiler/eclexia-modules/src/parallel.rs`: 1 unwrap (line 247 `expect_ok`)
- `compiler/eclexia-codegen/tests/pipeline_test.rs`: 18 unwraps
- `compiler/eclexia-codegen/tests/integration_test.rs`: 4 unwraps

The production-critical ones to fix are in parser, modules, and any non-test `.rs` files.

**What to do:**

1. Run `panic-attack assail . --output /tmp/eclexia-unwrap-audit.json` to get the current count.
2. In each non-test `.rs` file, replace `unwrap()` with proper error handling:
   - Use `?` operator where the function returns `Result`.
   - Use `.unwrap_or_default()` or `.unwrap_or_else(|| ...)` for cases where a fallback is acceptable.
   - Use `expect("descriptive message")` only where the invariant is truly guaranteed.
3. Focus on files in `compiler/eclexia/src/`, `compiler/eclexia-parser/src/`, `compiler/eclexia-modules/src/`, `compiler/eclexia-lsp/src/`.
4. Leave test files (`#[cfg(test)]` modules) as-is -- unwraps in tests are acceptable.
5. Target: reduce production unwraps by at least 50%.

**Verification:**
```bash
cargo clippy --workspace 2>&1 | grep -c "unwrap"
# Should be lower than before. Run panic-attack again:
# panic-attack assail . --output /tmp/eclexia-post-fix.json
# Compare weak point count with the 15 from 2026-02-09 scan.
cargo test --workspace --lib 2>&1 | tail -5
```

---

## TASK 12: Complete WASM backend complex type support (MEDIUM)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-wasm/src/lib.rs`

**Problem:** The WASM backend generates valid `.wasm` binaries for arithmetic and control flow, but the file header (lines 28-32) documents three major limitations:
1. Strings are stored in data section with fixed offsets (no GC/malloc)
2. Complex types (tuples, arrays, structs) not yet supported
3. No WASI integration

The `ty_to_wasm` function (line 156) returns `None` for any non-primitive type.

**What to do:**

1. **Tuples**: Represent as linear memory offsets. A tuple `(i32, f64)` is 12 bytes at a known offset. Emit `i32.store`/`f64.store` to write fields and corresponding loads to read.
2. **Arrays**: Represent as `(pointer: i32, length: i32)` in linear memory. Store elements contiguously. Emit bounds checking for index operations.
3. **Strings**: Already partially implemented via data section. Add proper length tracking -- strings should be `(offset: i32, length: i32)` pairs rather than fixed offsets.
4. Update `ty_to_wasm` to return `Some(WasmType::I32)` for complex types (they become pointers into linear memory).
5. Add a linear memory allocator (bump allocator) that tracks the next free offset in the WASM memory section.
6. Add tests: tuple creation/field access, array creation/indexing, string concatenation.

**Verification:**
```bash
cargo test -p eclexia-wasm --lib 2>&1 | tail -20
# Test WASM output:
echo 'def main() -> Unit { let t = (1, 2.0); println(int_to_string(t.0)) }' > /tmp/test_tuple.ecl
cargo run -- build --target wasm /tmp/test_tuple.ecl 2>&1
```

---

## TASK 13: Connect LLVM backend to runtime linking (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-llvm/src/lib.rs`

**Problem:** The LLVM backend generates textual `.ll` IR files and can optionally invoke `llc` to produce `.o` object files. However, the generated object files are not linked to the Eclexia runtime. The QUICK_STATUS.md (line 71) confirms "linking to runtime is still manual." The IR includes runtime hooks (`eclexia_rt_start`, `eclexia_rt_stop`, resource tracking metadata) but there is no C/Rust library that implements these symbols.

**What to do:**

1. Create a small C or Rust static library (`runtime/eclexia-rt-native/`) that implements the external symbols referenced in the LLVM IR:
   - `eclexia_rt_start()`: Initialize the runtime (shadow price registry, resource tracker).
   - `eclexia_rt_stop()`: Finalize and print resource usage summary.
   - `eclexia_rt_track_resource(resource_id: i64, amount: f64)`: Record resource usage.
   - `eclexia_rt_query_shadow_price(resource_id: i64) -> f64`: Return current shadow price.
2. Build this as a static library (`.a` file).
3. In the LLVM backend's `compile_to_native` function, add a linking step: `cc output.o -L<path> -leclexia_rt -o output`.
4. Add a test that compiles a simple function to native code via LLVM and runs it.

**Verification:**
```bash
cargo build --workspace 2>&1 | tail -5
# Test end-to-end LLVM compilation:
echo 'def main() -> Unit { println("hello from LLVM") }' > /tmp/test_llvm.ecl
cargo run -- build --target llvm /tmp/test_llvm.ecl 2>&1
# Should produce a .ll file. If llc is available:
# llc -O2 /tmp/test_llvm.ll -o /tmp/test_llvm.o
```

---

## TASK 14: Implement package registry server stub (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia/src/registry.rs` (125 lines)

**Problem:** The registry client exists and can fetch metadata, download tarballs, and verify checksums. However, there is no registry server. The client points to `https://registry.eclexia.dev` which does not exist. The STATE.scm lists package-registry completion at 0%.

**What to do:**

1. Create a minimal registry server in `/var/mnt/eclipse/repos/eclexia/runtime/eclexia-registry-server/` as a new crate. Use `eclexia-web-server` (587 lines, already in workspace) or `eclexia-rest` (393 lines) as the HTTP foundation.
2. Implement three endpoints:
   - `GET /packages/:name/:version` -- return package metadata JSON.
   - `GET /packages/:name/:version/download` -- serve the tarball.
   - `POST /packages` -- upload a new package (with authentication).
3. Use a flat filesystem backend: packages stored as `packages/<name>/<version>/metadata.json` and `packages/<name>/<version>/<name>-<version>.tar`.
4. Add the crate to the workspace `Cargo.toml`.
5. Add at least 2 integration tests: fetch metadata, download package.

**Verification:**
```bash
cargo build -p eclexia-registry-server 2>&1 | tail -5
cargo test -p eclexia-registry-server --lib 2>&1 | tail -10
```

---

## TASK 15: Add WASI integration to WASM backend (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/compiler/eclexia-wasm/src/lib.rs`

**Problem:** The WASM backend header (line 31) lists "No WASI integration yet" as a limitation. Without WASI, WASM modules cannot do file I/O, access environment variables, or interact with the system clock -- making the stdlib `io.ecl` and `time.ecl` modules unusable in WASM targets.

**What to do:**

1. Add WASI preview1 imports to the WASM module's import section:
   - `wasi_snapshot_preview1::fd_write` -- for `println`/`print` output.
   - `wasi_snapshot_preview1::clock_time_get` -- for timing.
   - `wasi_snapshot_preview1::args_get` / `args_sizes_get` -- for CLI args.
2. When compiling `println` calls in the WASM backend, emit calls to `fd_write` (fd=1 for stdout) instead of the current host import approach.
3. Add a `--wasi` flag to `build --target wasm` that enables WASI imports.
4. Test with `wasmtime` or `wasmer` to verify the output module runs correctly.
5. Add a test that compiles a hello-world program to WASM+WASI and validates the binary structure.

**Verification:**
```bash
cargo test -p eclexia-wasm --lib 2>&1 | tail -20
echo 'def main() -> Unit { println("hello WASI") }' > /tmp/test_wasi.ecl
cargo run -- build --target wasm --wasi /tmp/test_wasi.ecl 2>&1
# If wasmtime is available:
# wasmtime /tmp/test_wasi.wasm
```

---

## TASK 16: Increase code coverage from 17.92% toward 50% (MEDIUM)

**Files:** All crates, especially under-tested ones.

**Problem:** QUICK_STATUS.md (line 82) reports baseline code coverage at 17.92% with a target of 80%. The most under-tested areas based on the audit:
- `compiler/eclexia/src/commands.rs` -- the main CLI driver, very large, limited testing.
- `compiler/eclexia-interp/src/eval.rs` -- the interpreter, tested only through conformance tests.
- `compiler/eclexia-codegen/src/vm.rs` -- the VM, tested via integration tests but few unit tests.
- `runtime/eclexia-runtime/src/adaptive.rs` -- no tests at all (0 tests).
- `compiler/eclexia-fmt/src/printer.rs` -- formatter, minimal tests.

**What to do:**

1. Add unit tests for `adaptive.rs`:
   - Test `select_best` with MinimizeCost criteria.
   - Test `select_best` with Weighted criteria.
   - Test `select_best` with PreferPriority criteria.
   - Test budget filtering (candidate that exceeds budget is excluded).
   - Test empty candidates returns None.
2. Add unit tests for `vm.rs`:
   - Test each arithmetic instruction (Add, Sub, Mul, Div, Rem).
   - Test comparison instructions.
   - Test jump/branch instructions.
   - Test CallBuiltin for `println`, `to_string`, `abs`, `sqrt`.
3. Add tests for `printer.rs` (formatter):
   - Test formatting a function definition.
   - Test formatting a struct definition.
   - Test formatting match expressions.
4. Run coverage: `cargo llvm-cov --workspace --html` and check the report.

**Verification:**
```bash
cargo test --workspace --lib 2>&1 | tail -5
# Check test count increased:
cargo test --workspace --lib 2>&1 | grep "test result"
# Target: at least 320 tests (up from 271)
```

---

## TASK 17: Fix interop bridge configurations (LOW)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/interop/wokelang_bridge.toml`
- `/var/mnt/eclipse/repos/eclexia/interop/phronesis_bridge.toml`
- `/var/mnt/eclipse/repos/eclexia/interop/betlang_bridge.toml`
- `/var/mnt/eclipse/repos/eclexia/interop/affinescript_bridge.toml`
- `/var/mnt/eclipse/repos/eclexia/ffi/`

**Problem:** The interop directory contains 4 bridge configuration TOML files and an INTEROP_STATUS.md, but the `ffi/` directory (which should contain the Zig FFI implementations per the ABI/FFI standard) is empty or minimal. The bridge configs exist but there is no code that reads or validates them.

**What to do:**

1. Create a bridge configuration parser in `/var/mnt/eclipse/repos/eclexia/compiler/eclexia/src/interop.rs` that reads `*_bridge.toml` files.
2. Add a CLI command `eclexia interop check` that validates all bridge configurations:
   - Check that referenced FFI entry points exist.
   - Check that the target language repo exists locally.
   - Report missing or broken bridges.
3. Create the Zig FFI scaffolding in `ffi/zig/src/` per the ABI/FFI standard:
   - `eclexia_ffi.zig`: C-compatible wrappers for calling Eclexia runtime functions.
   - `build.zig`: Build configuration.
4. Generate C headers in `generated/abi/eclexia_ffi.h` from the Zig FFI signatures.

**Verification:**
```bash
cargo build --workspace 2>&1 | tail -5
# Test interop check (once implemented):
# cargo run -- interop check 2>&1
ls /var/mnt/eclipse/repos/eclexia/ffi/zig/src/
ls /var/mnt/eclipse/repos/eclexia/generated/abi/
```

---

## TASK 18: Update STATE.scm with honest completion percentages (HIGH)

**Files:**
- `/var/mnt/eclipse/repos/eclexia/STATE.scm`
- `/var/mnt/eclipse/repos/eclexia/.machine_readable/STATE.scm`

**Problem:** The root STATE.scm has not been updated since 2026-02-06. Several completion percentages are inaccurate:
- `codegen` listed at 95% -- accurate for bytecode, but Cranelift/LLVM/WASM have gaps.
- `cranelift-backend` listed at 15% -- should be ~70% (real codegen for most MIR constructs).
- `llvm-backend` listed at 0% -- should be ~50% (generates real `.ll` files, 21 tests).
- `wasm-backend` listed at 60% -- should be ~65% (generates real `.wasm`, but no complex types/WASI).
- `runtime-scheduler` listed at 70% -- should be ~85% (real implementation with 5 tests).
- `runtime-profiler` listed at 70% -- should be ~80% (real implementation, 6 tests, missing memory tracking).
- `runtime-carbon` listed at 70% -- should be ~90% (real implementation with providers, forecasting, 7+ tests).
- `runtime-shadow` listed at 70% -- should be ~85% (real implementation with LP duality pricing, 8+ tests).
- `shadow-prices` listed at 40% -- should be ~80% (real defaults, trend analysis, EMA).
- `package-registry` listed at 0% -- remains 0%.
- `overall-completion` listed at 67 -- should be ~60% after honest assessment.

**What to do:**

1. Update the root `STATE.scm` with corrected percentages as listed above.
2. Update the `updated` field to `"2026-02-12"`.
3. Update the `.machine_readable/STATE.scm` to mirror the root STATE.scm.
4. Update the `session-history` section with a new entry documenting this audit.
5. Ensure `QUICK_STATUS.md` completion line is consistent with STATE.scm.

**Verification:**
```bash
# Verify STATE.scm is valid Scheme:
guile -c '(load "/var/mnt/eclipse/repos/eclexia/STATE.scm")' 2>&1
# Or just check syntax:
grep "overall-completion" /var/mnt/eclipse/repos/eclexia/STATE.scm
```

---

## FINAL VERIFICATION

After all tasks are complete, run this full verification suite:

```bash
# 1. Build the entire workspace
cargo build --workspace 2>&1

# 2. Run all library tests
cargo test --workspace --lib 2>&1

# 3. Run conformance tests
cargo test -p eclexia --test conformance_tests 2>&1

# 4. Run clippy
cargo clippy --workspace 2>&1

# 5. Count remaining TODOs/stubs
grep -r "TODO\|FIXME\|HACK\|placeholder\|stub" --include="*.rs" /var/mnt/eclipse/repos/eclexia/compiler/ /var/mnt/eclipse/repos/eclexia/runtime/ /var/mnt/eclipse/repos/eclexia/libraries/ | grep -v target/ | grep -v "// Placeholder:" | wc -l

# 6. Count remaining Admitted proofs
grep -c "Admitted" /var/mnt/eclipse/repos/eclexia/formal/coq/src/*.v

# 7. Count unwraps in production code (excluding tests)
grep -r "\.unwrap()" --include="*.rs" /var/mnt/eclipse/repos/eclexia/compiler/ /var/mnt/eclipse/repos/eclexia/runtime/ | grep -v "#\[cfg(test)\]" | grep -v "mod tests" | grep -v "/target/" | wc -l

# 8. Verify all tests pass (should be 0 failures)
cargo test --workspace 2>&1 | grep "test result"

# 9. Security scan
# panic-attack assail /var/mnt/eclipse/repos/eclexia --output /tmp/eclexia-final-scan.json

# 10. Coverage check
# cargo llvm-cov --workspace --html
```

**Expected outcomes:**
- Build: 0 errors, 0 warnings
- Library tests: 320+ passing, 0 failures
- Conformance: 32/32 valid, 19/19 invalid, 0 skips
- Clippy: 0 warnings (or only lint-level suggestions)
- TODOs/stubs: fewer than 10 (down from ~35)
- Admitted proofs: 0 in Typing.v, 0-1 in ShadowPrices.v
- Production unwraps: fewer than 50 (down from ~100+)
