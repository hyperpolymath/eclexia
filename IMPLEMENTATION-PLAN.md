# Eclexia Implementation Plan: LLVM Backend & Production (Updated Feb 12, 2026)

**Date:** 2026-02-12
**Goal:** Deliver a real LLVM-native backend that emits `.ll`/`.o`, plugs into Eclexia's runtime for resource tracking, and cross-compiles cleanly on the major platforms.
**Status:** Bytecode tooling, the CLI, runtime instrumentation (scheduler, profiler, carbon, shadow price engine) and most of the compiler pipeline already work; the `llvm` target now emits `.ll`, invokes `llc`, surfaces artifacts/duration feedback, and records runtime tracking hooks. Reactive crates (`modules`, `tiered`, `db`) remain partially wired, and the documentation/infra audit (Quick Status, IMPLEMENTATION_ROADMAP updates) has already corrected overstatements from earlier milestones.

---

## Reality check
- Bytecode path, parser/typeck/MIR lowering, CLI/REPL, runtime subsystem (scheduler/profiler/carbon/shadow price), and the test suite (271 unit tests + 51 conformance tests) are verified and documented in `QUICK_STATUS.md` and `ECLEXIA-COMPLETE-STATUS-2026-02-09.md`.
- The current `eclexia build --target llvm` branch runs `LlvmBackend::generate`, writes `.ll`, invokes `llc` to produce `.o`, and prints artifact sizes/durations; `llc` failures now return a non-zero CLI exit and point to the generated `.ll` path with install guidance.
- Runtime instrumentation hooks are now emitted around native functions (`start_tracking`/`stop_tracking` declarations and calls are present), and preliminary `!eclexia.resource.*` metadata attachment for function resource constraints is in place; adaptive dispatch tables are still conceptual.
- Reactive compiler crates are partially wired into `build --analyze` (comptime/absinterp/specialize/effects boxed, while modules, db, tiered still need integration) and cross-platform packaging/infrastructure (PanLL, gitbot fleet, OPSM trust) remains TODO.

---

## Revised timeline
### Phase 0 — Foundations (Feb 7-10) [Complete]
- LLVM dependencies installed (`LLVM 17`, `inkwell`, `good_lp`, runtime libs) and `eclexia-llvm` crate scaffolded.
- Basic textual IR generator exists (`LlvmBackend::generate`, string interning, type mapping) and is wired into the CLI `llvm` target for reporting.
- Documentation and status dashboards (README, QUICK_STATUS, implementation roadmaps) were updated to reflect the honest completion state.

### Phase 1 — IR emission & CLI integration (Feb 11-18) [Completed]
- `commands::build --target llvm` now writes the full `LlvmModule::ir()` to `<input>.ll`, produces `<input>.o` via `llc`, captures opt level/durations, and surfaces artifact paths (`compiler/eclexia/src/commands.rs`).
- LLVM build now exits non-zero when `llc` fails, while still leaving `.ll` on disk with actionable diagnostics; integration test coverage includes the missing-`llc` failure path.
- Regression test `integration_llvm_native_target` builds `examples/hello_world.ecl`, runs `llc`, and asserts `.ll`/`.o` emission, preventing regression (`compiler/eclexia/tests/integration_tests.rs`).
- Documentation (`GETTING_STARTED.md`, `QUICK_STATUS.md`) now describes the LLVM workflow, install instructions for LLVM 17, and how to rerun `llc` manually when missing.
- **Phase 1 verification:** CLI smoke run `eclexia build examples/hello_world.ecl --target llvm` produces `.ll`/`.o`, prints opt level, and logs `llc` duration (`compiler/eclexia/src/commands.rs`); regression integration test `integration_llvm_native_target` confirms the workflow in CI (`compiler/eclexia/tests/integration_tests.rs`); docs referencing `GETTING_STARTED.md`/`QUICK_STATUS.md` allow anyone to reproduce the path manually and describe LLVM requirements/fallbacks so Phase 1 work stays traceable.

### Phase 2 — Type lowering & control-flow correctness (Feb 19-26)
- Ensure every MIR type (primitives, strings, resources, structs, adaptive metadata) lowers to a correct LLVM type, with padding/alignment and fat-pointer conventions for strings.
- Ensure locals/params are `alloca` + `load`/`store` with correct calling convention, including closures and `@adaptive` solutions that allocate captured env structs.
- Emit control flow primitives (`br`, `switch`, `phi`) that respect dominators and updates to `block_labels`, covering `if/else`, `while`, `for`, `match`, and `panic` paths.
- Add unit tests around `value_is_float`, `infer_value_llvm_type`, and `compile_function` for complex MIR fragments (loops + pattern matches).
- **Progress (2026-02-12):** `compiler/eclexia-llvm/src/lib.rs` now infers types for `Load`/`Field`/`Index` via MIR-aware helpers, avoids defaulting those paths to `i64`, emits typed loads (e.g., `load float, ptr ...`), and coerces non-boolean branch conditions / non-integer switch values into valid LLVM control-flow operands. Added regression tests for tuple field/index inference, array/string length field handling, resource float detection, typed loads, branch coercion, switch coercion, and unreachable branch edges.

### Phase 3 — Adaptive functions & runtime instrumentation (Mar 1-14)
- Emit one LLVM function per `@solution`, then build a dispatch wrapper that calls the scheduler/profiler runtime (shadow price scheduler selects solution, `start_tracking`/`stop_tracking` recorded).
- Attach metadata nodes for energy/carbon budgets per function so the runtime can introspect resource consumption (`@eclexia.resource.energy` metadata, etc.).
- Ensure runtime calls (e.g., `@eclexia_runtime_start_tracking`) are declared and emitted before/after natives, and update the `HealthServer` instrumentation to expose shadow prices from native executions.
- Continue wiring reactive crates (modules, db, tiered) so `build --analyze` sees LLVM-compiled artifacts and can annotate budgets/constraints in reports.
- **Progress (2026-02-12):** function-level `!eclexia.resource.*` metadata attachment and runtime tracking hook emission are now present in generated IR; remaining work is adaptive dispatch integration and runtime consumption of these metadata nodes.

### Phase 4 — Optimization & cross-compilation (Mar 15-31)
- Run LLVM opt passes (const-folding, DCE, inlining, vectorization) before invoking `llc`; capture pass logs when `--analyze` is on.
- Support cross-target builds (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, others as needed) and document required toolchains, linker flags, runtime lib paths, etc.
- Link generated object files with the runtime (`runtime/eclexia-runtime`) via `clang`/`gcc` wrappers to produce final executables or dynamic libraries.
- Add CI coverage for `--target llvm` (build + tests) and cross compile jobs.

---

## Milestones
- [x] Core toolchain (parser/typeck/MIR), runtime, CLI, tests, docs audited and stable (Priority 2 done, Quick Status honed).
- [x] `.ll` emitter + `llc` compile path (Phase 1 deliverable).
- [ ] Robust type lowering + control flow (Phase 2 deliverable).
- [ ] Adaptive functions + resource tracking instrumentation (Phase 3 deliverable).
- [ ] Optimized, cross-platform native packages (Phase 4 deliverable).

---

## Success criteria
- `eclexia build --target llvm` writes `.ll`, compiles with `llc`, and prints artifact sizes within CLI output.
- Generated LLVM IR includes hooks for `@eclexia_runtime_start_tracking`, `stop_tracking`, and `current_energy`, matching runtime instrumentation.
- Shadow-price-driven adaptive dispatch is visible in emitted IR/objects, with metadata nodes representing budget constraints.
- Native execution (with the runtime linked) reproduces the same outputs and resource reports as bytecode execution for `examples/hello_world.ecl` and key demos.
- CI exercises `--target llvm` on Linux/macOS, and documentation tells users how to install LLVM and run the target.

---

## Immediate next steps
1. Finish remaining Phase 2 control-flow depth: add explicit `phi`-sensitive tests (and lowering strategy where needed) for merged values across loops/matches so dominance assumptions stay explicit.
2. Connect emitted resource metadata to adaptive runtime decisions: thread `!eclexia.resource.*` data into scheduler/profiler health reporting and adaptive solution selection diagnostics.
3. Expand end-to-end native checks: add linked native execution tests comparing bytecode/runtime resource reports against LLVM native runs for key examples.

---

## Risks & mitigations
- **Missing `llc`/`clang` on contributors' systems:** fail fast with a clear non-zero `llc` error that includes install instructions (Homebrew `llvm@17`, `apt install llvm-17`, etc.) while still emitting `.ll` so contributors can rerun `llc` manually.
- **Resource instrumentation drift:** compare the bytecode-run resource log vs. native run for the same example; add golden JSON fixtures for `current_energy()` and `current_carbon()` to ensure the runtime hooks fire and report comparable values.
- **Cross-compilation complexity:** keep the arm64/macOS targets in a separate branch until Linux artifacts succeed, reuse existing runtime health server for readiness/liveness.

---

## Notes
- Reactive crate wiring (modules, db, tiered) and infrastructure enrolment (gitbot fleet, PanLL, OPSM trust) are tracked in `ECLEXIA-COMPLETE-STATUS-2026-02-09.md`; reference that document when choosing follow-up work.
- Update `QUICK_STATUS.md` after Phase 1 so the status page says "LLVM target emits `.ll` and runs `llc`".
- This plan is the working record of the native-target effort; annotate it as things move from TODO → DONE so downstream agents can pick up exactly where this session leaves off.
