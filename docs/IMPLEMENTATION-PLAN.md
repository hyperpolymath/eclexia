# Eclexia Implementation Plan: LLVM Backend & Production (Updated Feb 11, 2026)

**Date:** 2026-02-11
**Goal:** Deliver a real LLVM-native backend that emits `.ll`/`.o`, plugs into Eclexia's runtime for resource tracking, and cross-compiles cleanly on the major platforms.
**Status:** Bytecode tooling, the CLI, runtime instrumentation (scheduler, profiler, carbon, shadow price engine) and most of the compiler pipeline already work; `llvm` target currently only reports estimated sizes and does not emit or link runnable code. Reactive crates (`modules`, `tiered`, `db`) are partially wired, and the documentation/infra audit (Quick Status, IMPLEMENTATION_ROADMAP updates) has already corrected overstatements from earlier milestones.

---

## Reality check
- Bytecode path, parser/typeck/MIR lowering, CLI/REPL, runtime subsystem (scheduler/profiler/carbon/shadow price), and the test suite (271 unit tests + 51 conformance tests) are verified and documented in `QUICK_STATUS.md` and `ECLEXIA-COMPLETE-STATUS-2026-02-09.md`.
- The current `eclexia build --target llvm` branch runs `LlvmBackend::generate` for heuristics and prints numeric estimates; it never writes `.ll` or runs `llc`, so no native artifact exists yet.
- Runtime instrumentation exists but is not wired to the LLVM emission pipeline (no `start_tracking`/`stop_tracking` hooks around native functions, adaptive dispatch tables are still conceptual, metadata points at runtime constants only in comments).
- Reactive compiler crates are partially wired into `build --analyze` (comptime/absinterp/specialize/effects boxed, while modules, db, tiered still need integration) and cross-platform packaging/infrastructure (PanLL, gitbot fleet, OPSM trust) remains TODO.

---

## Revised timeline
### Phase 0 — Foundations (Feb 7-10) [Complete]
- LLVM dependencies installed (`LLVM 17`, `inkwell`, `good_lp`, runtime libs) and `eclexia-llvm` crate scaffolded.
- Basic textual IR generator exists (`LlvmBackend::generate`, string interning, type mapping) and is wired into the CLI `llvm` target for reporting.
- Documentation and status dashboards (README, QUICK_STATUS, implementation roadmaps) were updated to reflect the honest completion state.

### Phase 1 — IR emission & CLI integration (Feb 11-18)
- Make `build --target llvm` write the full `LlvmModule::ir()` into a `.ll` file by default, using the same folder as the input when `--output` is omitted.
- Invoke `llc` (if available) to produce an object file; capture its status so we know failures are from LLVM instead of the CLI.
- Surface the output paths (IR + object) and `llc` opt level in CLI feedback, plus total sizes and durations.
- Add a regression test (e.g., build `examples/hello_world.ecl` with `--target llvm`, run `llc`, and check for success) so the integration path stays guarded.
- Document the new workflow in `GETTING_STARTED.md`/`QUICK_STATUS.md` so the broader team understands how to reproduce the native build.

### Phase 2 — Type lowering & control-flow correctness (Feb 19-26)
- Ensure every MIR type (primitives, strings, resources, structs, adaptive metadata) lowers to a correct LLVM type, with padding/alignment and fat-pointer conventions for strings.
- Ensure locals/params are `alloca` + `load`/`store` with correct calling convention, including closures and `@adaptive` solutions that allocate captured env structs.
- Emit control flow primitives (`br`, `switch`, `phi`) that respect dominators and updates to `block_labels`, covering `if/else`, `while`, `for`, `match`, and `panic` paths.
- Add unit tests around `value_is_float`, `infer_value_llvm_type`, and `compile_function` for complex MIR fragments (loops + pattern matches).

### Phase 3 — Adaptive functions & runtime instrumentation (Mar 1-14)
- Emit one LLVM function per `@solution`, then build a dispatch wrapper that calls the scheduler/profiler runtime (shadow price scheduler selects solution, `start_tracking`/`stop_tracking` recorded).
- Attach metadata nodes for energy/carbon budgets per function so the runtime can introspect resource consumption (`@eclexia.resource.energy` metadata, etc.).
- Ensure runtime calls (e.g., `@eclexia_runtime_start_tracking`) are declared and emitted before/after natives, and update the `HealthServer` instrumentation to expose shadow prices from native executions.
- Continue wiring reactive crates (modules, db, tiered) so `build --analyze` sees LLVM-compiled artifacts and can annotate budgets/constraints in reports.

### Phase 4 — Optimization & cross-compilation (Mar 15-31)
- Run LLVM opt passes (const-folding, DCE, inlining, vectorization) before invoking `llc`; capture pass logs when `--analyze` is on.
- Support cross-target builds (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, others as needed) and document required toolchains, linker flags, runtime lib paths, etc.
- Link generated object files with the runtime (`runtime/eclexia-runtime`) via `clang`/`gcc` wrappers to produce final executables or dynamic libraries.
- Add CI coverage for `--target llvm` (build + tests) and cross compile jobs.

---

## Milestones
- [x] Core toolchain (parser/typeck/MIR), runtime, CLI, tests, docs audited and stable (Priority 2 done, Quick Status honed).
- [ ] `.ll` emitter + `llc` compile path (Phase 1 deliverable).
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
1. Expand `commands::build` `target == "llvm"` branch so it writes `LlvmModule::ir()` to a `.ll` file (respecting `--output`), runs `llc` (if on PATH), and surfaces success/failure status with artifact paths and durations.
2. Add a regression (maybe in `tests/cli.rs` or a new `eclexia-llvm` integration test) that builds `examples/hello_world.ecl` with `--target llvm`, runs `llc`, and checks for an object file; fail the test if `llc` is absent or returns non-zero.
3. Document the fluent path in `GETTING_STARTED.md` / `QUICK_STATUS.md`, mentioning the default LLVM opt level, fallback when `llc` is missing, and how to run the resulting native binary.
4. Keep this plan updated: after 1-3 land, mark Phase 1 complete, move to Phase 2 tasks, and note any blockers or new discoveries in the plan itself.

---

## Risks & mitigations
- **Missing `llc`/`clang` on contributors' systems:** detect the absence, print a human-readable warning with install instructions (Homebrew `llvm@17`, `apt install llvm-17`, etc.), and skip the compile step while still emitting `.ll` so the artifact exists.
- **Resource instrumentation drift:** compare the bytecode-run resource log vs. native run for the same example; add golden JSON fixtures for `current_energy()` and `current_carbon()` to ensure the runtime hooks fire and report comparable values.
- **Cross-compilation complexity:** keep the arm64/macOS targets in a separate branch until Linux artifacts succeed, reuse existing runtime health server for readiness/liveness.

---

## Notes
- Reactive crate wiring (modules, db, tiered) and infrastructure enrolment (gitbot fleet, PanLL, OPSM trust) are tracked in `ECLEXIA-COMPLETE-STATUS-2026-02-09.md`; reference that document when choosing follow-up work.
- Update `QUICK_STATUS.md` after Phase 1 so the status page says "LLVM target emits `.ll` and runs `llc`".
- This plan is the working record of the native-target effort; annotate it as things move from TODO → DONE so downstream agents can pick up exactly where this session leaves off.
