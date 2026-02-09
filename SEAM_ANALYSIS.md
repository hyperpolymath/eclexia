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
