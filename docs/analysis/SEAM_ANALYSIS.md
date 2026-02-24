# Seam Analysis Report — 2026-02-09

Audit of crate boundaries for type safety, error propagation, and coverage.

## Issues Found

### Fixed This Session

| # | Severity | Location | Issue | Fix |
|---|----------|----------|-------|-----|
| 1 | Critical | eclexia-mir/src/lower.rs:98 | `panic!("No current function")` | Changed to `.expect()` with ICE message |
| 2 | Critical | eclexia-mir/src/lower.rs:222 | `.unwrap()` on function extraction | Changed to `.expect()` with ICE message |

### Known — Not Yet Fixed

| # | Severity | Location | Issue | Notes |
|---|----------|----------|-------|-------|
| 3 | Medium | eclexia-hir/src/lower.rs:1015-1038 | Concurrency AST nodes lowered to Unit | spawn, channel, send, recv, select, yield, MacroCall |
| 4 | Medium | eclexia-hir/src/lower.rs:980-986 | Await/Handle stripped to identity | Loses async/effect semantics |
| 5 | Low | eclexia-fmt/src/printer.rs:924-929 | Concurrency uses `/* placeholder */` comments | Formatting incomplete |
| 6 | Low | eclexia-lint/src/rules/unused_variable.rs | Assign targets not traversed | False positive risk |
| 7 | Low | eclexia-hir/src/lower.rs:1012 | Error nodes → Unit literal | Loses error span info |
| 8 | Info | hir::LocalId vs mir::LocalId | Arena Idx vs raw u32 | Explicit mapping exists, works correctly |

## Seams Verified Clean

- Lexer → Parser: Token stream consumed correctly
- Parser → AST: Parse errors create Error placeholders
- AST → TypeChecker: Robinson unification covers all ExprKinds
- HIR → MIR: Resource constraints properly lowered
- MIR → Codegen: Instruction emission uses arena indices
- Codegen → VM: Bytecode correctly mapped
- LSP ↔ Compiler: Diagnostics converted via span info
- Runtime ↔ Interp: Shadow prices, resources integrate cleanly

## Seam 12.2: Compiler → Runtime Boundary

- `eclexia/src/commands.rs` wires the CLI to `eclexia_runtime::Runtime`: `run_bytecode`, `serve_health`, and `profile` all construct a new `Runtime`, call `ingest_usage` with `VirtualMachine::get_resources()` tuples, refresh shadow prices, and feed `PowerMetrics` into the carbon report path. That single `Runtime` instance is shared with the `HealthServer` probe, so resource tracking and shadow pricing remain consistent across CLI commands.
- The runtime crate exposes `RuntimeConfig`, `ShadowPriceRegistry`, and resource tracking helpers built on the same `Dimension` enum as the compiler (`eclexia_ast::dimension::Dimension`), so there is no type mismatch when the bytecode backend pushes (`SmolStr`, `Dimension`, `f64`) triples into `Runtime::ingest_usage`.
- Observed limitation: interpreter execution currently only logs placeholder carbon metrics and does not ingest its resource tracker into `Runtime`, so the shadow-price/carbon output path remains incomplete (see the `carbon_report` block in `run()` for the interpreter path).

## Seam 12.3: Stdlib → Interpreter Builtins

- The standard library peppers core modules (`stdlib/core.ecl`, `stdlib/collections.ecl`, `stdlib/io.ecl`, `stdlib/text.ecl`, `stdlib/math.ecl`, `stdlib/time.ecl`, etc.) with `@builtin(...)` annotations for primitives such as `array_len`, `array_set`, `string_len`, `int_to_string`, `parse_json`, `time_now_ms`, etc.
- `compiler/eclexia-interp/src/builtins.rs` registers a subset of those primitive names (math, string transformations, JSON/file I/O, collection helpers, and set operations) with matching native implementations, ensuring the interpreter can satisfy the majority of `@builtin` calls that appear at runtime.
- Notable gaps remain: `array_len`, `array_get`, `array_push`, `array_pop`, `string_len`, `string_concat`, `string_substring`, and the `int_to_string` / `float_to_string` / `string_to_int` / `string_to_float` conversions declared in `stdlib/core.ecl` are not yet registered in `builtins::register`, which means the interpreter path will hit "unknown builtin" errors when executing the fully realized stdlib.
- Action items: implement these missing primitives or reroute stdlib helpers through interpreter-safe replacements so the seam stays sound for interpreter execution.

## Seam 12.4: LSP → Compiler Integration

- `compiler/eclexia-lsp/src/server.rs` repeatedly invokes `eclexia_parser::parse`, `eclexia_typeck::check`, `eclexia_lint::Linter::lint`, and `symbols::SymbolTable::build` while handling diagnostics, completion, hover, definition, reference, and document-symbol requests, so the LSP server directly reuses the same parser + type checker stack that the compiler uses for CLI commands.
- Hover/completion/definition handlers consult the symbol table generated from each AST (symbol positions, doc comments, types), then format responses via `tower_lsp` using the compiler’s `Span` helpers, so the seam enforces that any language change in the compiler is reflected immediately in the IDE surface without separate duplication.
- A remaining risk is that the LSP server re-parses the document from scratch on each change rather than reusing incremental caches, so edits may temporarily show stale diagnostics until the next `did_change` cycle finishes.

## Seam 12.5: Reactive Crates → Main Pipeline

- The `run_mir_analysis` helper in `compiler/eclexia/src/commands.rs` calls into the reactive crates: `eclexia_comptime::const_fold` + `resource_verify`, `eclexia_absinterp::resource` for resource bounds and budget verification, `eclexia_specialize::binding_time` for specialization detection, `eclexia_effects::evidence::EffectRegistry` for effect signatures, `eclexia_modules::parallel` for module graph importing, `eclexia_tiered::tier::TierManager` for tiered execution, and `eclexia_db` for the Salsa database diagnostics.
- Each crate returns structured results that are iterated and printed inside the CLI, so their interfaces (function signatures, result types, and error handling) are exercised end-to-end on every `eclexia build --analyze` invocation; the typed bindings ensure there is no accidental coupling beyond the declared API.
- As an honesty note, the tiered execution analysis currently uses heuristics (instruction counts + recursion) rather than runtime telemetry, so while the seam is wired, its invariants still depend on continuing to refine the heuristics for real workloads.
