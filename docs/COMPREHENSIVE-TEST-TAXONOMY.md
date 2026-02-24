<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

# Eclexia: Comprehensive Test Taxonomy

Every category of test that should be performed on the eclexia language,
from syntax fuzzing to economic model validation. Organised by phase.

Current status marked: [DONE], [PARTIAL], [TODO], [NEEDS-SUPERFUZZER]

---

## Phase 1: LEXER TESTS

### 1.1 Token Recognition [PARTIAL]
- Every keyword produces correct token (48 keywords)
- Every operator produces correct token (30+ operators)
- Every literal type: int, float, string, char, bool, unit
- Resource literals: `100J`, `50ms`, `1gCO2`, `2.5kWh`
- Dimensional suffixes: all units in dimension.rs
- Unicode identifiers: Greek, CJK, emoji (if allowed)
- String escapes: `\n`, `\t`, `\\`, `\"`, `\0`, `\x41`, `\u{1F600}`
- Raw strings, multiline strings, string interpolation
- Comments: line `//`, block `/* */`, doc `///`, `//!`
- Nested block comments `/* /* */ */`

### 1.2 Lexer Edge Cases [TODO]
- Maximum token length (very long identifiers, very long strings)
- Maximum integer literal (overflow detection)
- Float precision edge cases: `0.0`, `-0.0`, `inf`, `NaN`
- Empty input
- Input that is only whitespace
- Input that is only comments
- Unterminated string literal
- Unterminated block comment
- Invalid UTF-8 sequences
- Null bytes in source
- BOM (byte order mark) handling
- Very long lines (10K+ characters)
- Mixed line endings (CRLF, LF, CR)

### 1.3 Lexer Fuzzing [NEEDS-SUPERFUZZER]
- Random byte sequences
- Mutated valid token streams
- Grammar-aware fuzzing of token boundaries
- Stress test: millions of tokens

---

## Phase 2: PARSER TESTS

### 2.1 Grammar Coverage [PARTIAL]
- Every production rule exercised at least once
- Every expression form: literal, var, binary, unary, call, if, match, block, tuple, array, index, field, lambda, struct, resource, cast, try, borrow, deref, async, await, handle, method call, path
- Every statement form: let, expr, return, while, for, assign, loop, break, continue
- Every item form: function, adaptive function, const, typedef (struct, enum, alias), import, trait, impl, module, static, effect, extern
- Every pattern form: var, wildcard, tuple, constructor, struct, binding, reference, or, slice, literal, range, rest
- Every constraint form: resource constraint, predicate constraint
- Every annotation: `@requires`, `@provides`, `@solution`, `@when`, `@optimize`
- Visibility modifiers: pub, pub(crate), private
- Generic type parameters: `<T>`, `<T, U>`, `<T: Bound>`
- Where clauses
- Closures with captures
- Operator precedence (all combinations)
- Associativity (left, right, none)

### 2.2 Parser Edge Cases [TODO]
- Deeply nested expressions (1000+ levels)
- Very long parameter lists
- Very many match arms
- Empty blocks, empty functions, empty modules
- Trailing commas everywhere they're allowed
- Missing semicolons (error recovery)
- Mismatched brackets (error recovery)
- Unexpected EOF in every position
- Ambiguous parses (ensure correct resolution)
- Maximum file size the parser can handle
- Unicode in all identifier positions
- Keywords as field names (if allowed)
- Reserved words in various positions

### 2.3 Parser Error Recovery [TODO]
- Continue parsing after syntax error
- Report multiple errors per file
- Don't cascade errors (one error shouldn't cause 50 more)
- Reasonable error messages for common mistakes
- Suggestion hints ("did you mean...?")

### 2.4 Parser Fuzzing [NEEDS-SUPERFUZZER]
- Grammar-based fuzzing (generate random valid/near-valid programs)
- Mutation-based fuzzing of valid programs
- Crash detection (parser should never panic on any input)
- Memory usage bounds
- Parse time bounds (no exponential blowup)

---

## Phase 3: TYPE CHECKER TESTS

### 3.1 Type Inference [PARTIAL]
- Let binding inference: `let x = 42` → Int
- Function return type inference
- Generic function instantiation: `identity(42)` → Int
- Lambda parameter inference from context
- Array element type inference
- Tuple type inference
- If-else branch unification
- Match arm type unification

### 3.2 Type Checking Correctness [PARTIAL]
- Primitive type operations: Int+Int, Float*Float, String+String, Bool&&Bool
- Type mismatch detection: Int+String, Bool*Float
- Function argument count checking
- Function argument type checking
- Return type checking
- Pattern exhaustiveness (match covers all cases)
- Pattern type checking (constructor matches scrutinee)
- Struct field type checking
- Method resolution order
- Trait bound checking
- Generic constraint satisfaction

### 3.3 Dimensional Type Checking [PARTIAL]
- Same-dimension addition: Energy + Energy = Energy
- Cross-dimension rejection: Energy + Time = ERROR
- Dimension multiplication: Energy * Time = Energy*Time
- Dimension division: Energy / Time = Power
- Scalar multiplication: Energy * Float = Energy
- Unit validation: J is Energy, ms is Time, gCO2 is Carbon
- Resource constraint validation: `@requires: energy < 100J`
- Resource provision validation: `@provides: energy: 80J`

### 3.4 Type System Edge Cases [TODO]
- Recursive types (type T = List<T>)
- Mutually recursive types
- Infinite type detection (occurs check)
- Higher-kinded types (if supported)
- Variance (covariant, contravariant, invariant)
- Subtyping (if supported)
- Type aliases in complex positions
- Generic type alias instantiation
- Associated types in traits
- Overlapping impl blocks
- Orphan rules (if any)

### 3.5 Type Checker Fuzzing [NEEDS-SUPERFUZZER]
- Random well-formed ASTs
- Random type annotations
- Constraint solver stress testing
- Type variable explosion detection

---

## Phase 4: SEMANTIC ANALYSIS TESTS

### 4.1 Name Resolution [PARTIAL]
- Local variable scoping (block scope)
- Function scope
- Module scope
- Import resolution
- Name shadowing
- Unused variable detection
- Undefined variable detection with suggestions

### 4.2 Control Flow Analysis [TODO]
- Unreachable code detection
- Missing return paths
- Break/continue outside loop
- Return outside function
- Infinite loop detection
- Dead code elimination opportunities

### 4.3 Borrow/Ownership Analysis [TODO]
- Mutable borrow exclusivity (if eclexia enforces this)
- Use-after-move detection
- Dangling reference detection
- Lifetime analysis (if applicable)

### 4.4 Effect Checking [TODO]
- Effect annotation correctness
- Unhandled effects
- Effect polymorphism
- Effect row operations

---

## Phase 5: RESOURCE SYSTEM TESTS (ECLEXIA-SPECIFIC)

### 5.1 Constraint Satisfaction [PARTIAL]
- Energy constraint within budget → success
- Energy constraint exceeded → reject
- Time/latency constraint within budget → success
- Time/latency constraint exceeded → reject
- Carbon constraint within budget → success
- Carbon constraint exceeded → reject
- Memory constraint within budget → success
- Memory constraint exceeded → reject
- Multiple constraints simultaneously
- Nested function constraints (caller budget >= sum of callee budgets)

### 5.2 Adaptive Function Selection [PARTIAL]
- Two solutions, select lower cost
- Three solutions, select by optimization criterion
- Conditional solutions (@when predicates)
- No feasible solution → error
- All solutions feasible → pick optimal
- Equal-cost solutions → deterministic tiebreak
- Nested adaptive functions
- Adaptive function as argument to higher-order function

### 5.3 Shadow Price Computation [TODO]
- Shadow price is non-negative
- Shadow price increases as resource becomes scarce
- Shadow price is zero when resource is abundant
- Shadow price across function boundaries
- Shadow price in loops (accumulation)
- Shadow price with multiple resource types simultaneously
- Shadow price convergence (does it stabilize?)
- Shadow price under constraint changes

### 5.4 Resource Tracking Accuracy [TODO]
- Track energy across function calls
- Track energy across loops
- Track energy across recursion
- Track multiple resources simultaneously
- Resource tracking in closures
- Resource tracking in async blocks
- Resource tracking overhead measurement
- Resource budget propagation (caller to callee)

### 5.5 Economic Model Validation [TODO]
- Pareto optimality of solution selection
- Monotonicity of shadow prices
- Complementary slackness conditions
- Dual feasibility
- Weak duality theorem verification
- Strong duality (when applicable)
- Sensitivity analysis (how do shadow prices change with budget?)

---

## Phase 6: INTERPRETER TESTS

### 6.1 Expression Evaluation [PARTIAL]
- Arithmetic: +, -, *, /, %, ** for Int and Float
- Comparison: ==, !=, <, <=, >, >= for all comparable types
- Boolean: &&, ||, ! with short-circuit evaluation
- Bitwise: &, |, ^, <<, >> for integers
- String concatenation
- Array operations: indexing, length, push, pop
- Tuple operations: creation, field access
- Struct operations: creation, field access, method calls
- Pattern matching: all pattern forms
- Closures: capture by value/reference
- Recursion: direct and mutual

### 6.2 Statement Execution [PARTIAL]
- Let binding (immutable and mutable)
- Assignment to mutable variables
- While loops with break/continue
- For loops over ranges and arrays
- Return from functions (early and normal)
- Nested scoping

### 6.3 Builtin Functions [PARTIAL]
- println, print (variadic)
- assert (true → unit, false → panic)
- len (arrays, strings)
- to_string (all types)
- range(start, end) → array
- All collection builtins (hashmap, sortedmap, queue, priority_queue, set)
- shadow_price (resource intrinsic)

### 6.4 Interpreter Edge Cases [TODO]
- Stack overflow from deep recursion
- Integer overflow behaviour
- Division by zero
- Index out of bounds
- Null/None dereference
- Very large arrays
- Very deep nesting
- Infinite loops (timeout/resource limit)
- Unicode in string operations
- Empty collections edge cases

### 6.5 Interpreter Fuzzing [NEEDS-SUPERFUZZER]
- Random valid programs (generated from grammar)
- Execution time bounds (no program runs forever)
- Memory bounds (no program consumes infinite memory)
- Crash detection (interpreter should never segfault)

---

## Phase 7: BYTECODE COMPILER & VM TESTS

### 7.1 Bytecode Generation [TODO]
- Every opcode generated correctly
- Instruction encoding/decoding roundtrip
- Constant pool management
- Jump target calculation
- Function call convention
- Stack frame management
- Resource tracking instruction generation

### 7.2 VM Execution [TODO]
- Every opcode executes correctly
- Stack overflow detection
- Stack underflow detection
- Invalid opcode handling
- Bytecode/interpreter result equivalence (same program, same output)
- VM state consistency after errors

### 7.3 VM Performance [TODO]
- Instructions per second measurement
- Memory allocation patterns
- GC pressure (if applicable)
- Comparison with interpreter performance

---

## Phase 8: COMPILER PIPELINE INTEGRATION TESTS

### 8.1 End-to-End Tests [PARTIAL]
- Parse → TypeCheck → Interpret (run command) — 29/32 passing
- Parse → TypeCheck → HIR → MIR → Bytecode → VM (build command)
- Parse → Format → Parse roundtrip (formatter preserves semantics)
- Parse → Lint (linter finds issues)
- Conformance test suite: valid programs succeed, invalid programs fail

### 8.2 Error Reporting [TODO]
- Errors point to correct source location
- Error messages are human-readable
- Errors include helpful hints/suggestions
- Multiple errors reported (not just first)
- No error cascading (one error doesn't cause dozens)
- Warnings vs errors distinction
- Error codes for programmatic handling

### 8.3 Pipeline Consistency [TODO]
- Interpreter and VM produce identical results
- TypeChecker accepts everything the interpreter can run
- TypeChecker rejects everything that would crash the interpreter
- Formatter output is idempotent (format(format(x)) == format(x))
- Linter doesn't false-positive on valid programs

---

## Phase 9: STANDARD LIBRARY TESTS

### 9.1 Core Module [TODO]
- All exported functions work correctly
- Type signatures match documentation
- Edge cases handled (empty inputs, nulls, overflows)
- Resource annotations accurate

### 9.2 Collections Module [PARTIAL]
- HashMap: new, insert, get, remove, contains, len, keys, values, entries
- SortedMap: new, insert, get, remove, len, keys, min_key, max_key, range
- Queue: new, enqueue, dequeue, peek, len, is_empty
- PriorityQueue: new, push, pop, peek, len
- Set: union, intersection, difference, symmetric_difference, is_subset, from_array

### 9.3 Math Module [TODO]
- Trigonometric functions
- Exponential/logarithmic functions
- Statistical functions
- Matrix operations (if included)
- Numerical precision

### 9.4 I/O Module [TODO]
- File read/write
- Console I/O
- Network I/O (if included)
- Error handling for I/O failures

### 9.5 Text Module [TODO]
- String manipulation
- Regex (if included)
- Unicode normalization
- Encoding/decoding

---

## Phase 10: TOOLING TESTS

### 10.1 Formatter Tests [PARTIAL]
- Idempotency (formatting twice = formatting once)
- All construct types formatted correctly
- Preserves semantics (formatted code has same behaviour)
- Handles comments correctly
- Configuration options work

### 10.2 Linter Tests [PARTIAL]
- Each lint rule triggers on bad code
- Each lint rule doesn't trigger on good code
- Suggested fixes are correct
- Configuration (enable/disable rules) works

### 10.3 LSP Tests [TODO]
- Diagnostics appear for type errors
- Completion suggestions are relevant
- Go-to-definition jumps to correct location
- Find-references finds all references
- Rename refactoring works correctly
- Hover shows correct type info
- Signature help shows correct params
- Formatting via LSP matches standalone formatter

### 10.4 Debugger Tests [TODO]
- Breakpoints stop at correct line
- Step-over advances one statement
- Step-into enters function calls
- Continue runs to next breakpoint
- Variable inspection shows correct values
- Call stack is accurate
- Resource inspection shows current budgets

### 10.5 Package Manager Tests [TODO]
- Manifest parsing
- Dependency resolution
- Version constraint satisfaction
- Lock file generation
- Registry client (when server exists)

---

## Phase 11: BENCHMARKS (ECLEXIA-SPECIFIC)

### 11.1 Resource Tracking Overhead [TODO]
- Fibonacci(30) with vs without resource annotations
- Sort 10K elements with vs without resource tracking
- Matrix multiply 100x100 with vs without tracking
- Measure: time overhead, memory overhead

### 11.2 Shadow Price Computation [TODO]
- Shadow price with 1, 10, 100, 1000 constraints
- Shadow price convergence time
- Shadow price memory usage
- Shadow price accuracy vs analytical solution

### 11.3 Adaptive Function Selection [TODO]
- Selection time with 2, 5, 10, 50 solutions
- Selection with simple vs complex @when predicates
- Nested adaptive function overhead

### 11.4 Compilation Speed [TODO]
- Parse time vs file size (100, 1K, 10K, 100K lines)
- Type check time vs file size
- Full pipeline time vs file size
- Incremental recompilation time (with eclexia-db)

### 11.5 VM Throughput [TODO]
- Instructions per second (tight loop)
- Function call overhead
- Comparison vs Python, Ruby, Lua bytecode VMs
- Memory allocation throughput

### 11.6 Comparison Benchmarks [TODO]
- Same algorithm in eclexia vs Rust vs Python vs JavaScript
- Focus on: execution time, memory usage, code size
- Show: resource tracking adds X% overhead for Y% insight

---

## Phase 12: SECURITY TESTS

### 12.1 Input Validation [TODO]
- Malformed source files don't crash compiler
- Very large files don't cause OOM
- Deeply nested structures don't cause stack overflow
- Adversarial inputs (designed to trigger worst-case behaviour)
- No information leakage in error messages

### 12.2 Dependency Audit [PARTIAL]
- `cargo audit` passes (bytes CVE fixed)
- All dependencies use compatible licenses
- No known malicious dependencies
- Supply chain verification (SHA-pinned)

### 12.3 Runtime Safety [TODO]
- Resource limits prevent denial-of-service
- No arbitrary code execution from .ecl files
- Sandbox escapes impossible
- File system access controlled

### 12.4 Fuzzing Campaigns [NEEDS-SUPERFUZZER]
- AFL/libFuzzer on lexer
- AFL/libFuzzer on parser
- AFL/libFuzzer on type checker
- AFL/libFuzzer on interpreter
- AFL/libFuzzer on VM
- Coverage-guided fuzzing until saturation
- Crash triage and fix verification

---

## Phase 13: FORMAL VERIFICATION

### 13.1 Type Safety Proofs [PARTIAL - 22 Admitted]
- Progress theorem: well-typed programs don't get stuck
- Preservation theorem: reduction preserves types
- Soundness of dimensional type system
- Soundness of resource constraint checking
- Correctness of unification algorithm
- Termination of type inference

### 13.2 Resource System Proofs [TODO]
- Shadow price non-negativity
- Shadow price monotonicity
- Complementary slackness
- Dual feasibility
- Budget propagation correctness
- Adaptive selection optimality

### 13.3 Compiler Correctness [TODO]
- Interpreter and VM semantic equivalence
- HIR lowering preserves semantics
- MIR lowering preserves semantics
- Bytecode generation preserves semantics
- Optimisation passes preserve semantics

---

## Phase 14: PROPERTY-BASED TESTING

### 14.1 Algebraic Properties [TODO]
- Commutativity: a + b == b + a for Int, Float
- Associativity: (a + b) + c == a + (b + c)
- Identity: a + 0 == a, a * 1 == a
- Distributivity: a * (b + c) == a*b + a*c
- Dimensional algebra: (Energy * Time) / Time == Energy

### 14.2 Roundtrip Properties [TODO]
- parse(format(parse(x))) == parse(x)
- serialize(deserialize(x)) == x (when bytecode serialization exists)
- compile(source) produces same output as interpret(source)

### 14.3 Monotonicity Properties [TODO]
- More resource budget → more solutions feasible
- Tighter constraints → fewer solutions feasible
- Shadow price monotonically increases as resource depletes
- Compilation time monotonically increases with file size (no pathological cases)

---

## Phase 15: REGRESSION TESTS

### 15.1 Bug Reproduction [TODO]
- Every fixed bug gets a test that would have caught it
- Conformance test regression (2026-02-09) → covered
- Binary ambiguity (eclexia vs eclexia-lsp) → covered
- Missing builtins in type checker → covered

### 15.2 Performance Regression [TODO]
- Benchmark suite run on every commit
- Alert if compilation time increases >10%
- Alert if runtime performance decreases >5%
- Alert if memory usage increases >10%

---

## Phase 16: CROSS-PLATFORM TESTS

### 16.1 OS Compatibility [TODO]
- Linux x86_64 (primary)
- macOS ARM64
- macOS x86_64
- Windows x86_64
- FreeBSD (stretch goal)

### 16.2 Architecture Compatibility [TODO]
- x86_64 (primary)
- ARM64/AArch64
- WASM (via eclexia-wasm backend)
- RISC-V (stretch goal)

---

## Phase 17: DOCUMENTATION TESTS

### 17.1 Code Examples [TODO]
- Every code example in documentation compiles and runs
- Every code example in README works
- Every code example in tutorials works
- REPL examples produce shown output

### 17.2 API Documentation [TODO]
- Every public function has documentation
- Every documented function's signature matches implementation
- Examples in doc comments compile

---

## Summary

| Phase | Tests | Status | Needs Superfuzzer? |
|-------|-------|--------|--------------------|
| 1. Lexer | ~50 | PARTIAL | Yes (1.3) |
| 2. Parser | ~80 | PARTIAL | Yes (2.4) |
| 3. Type Checker | ~60 | PARTIAL | Yes (3.5) |
| 4. Semantic Analysis | ~30 | TODO | No |
| 5. Resource System | ~40 | PARTIAL | No |
| 6. Interpreter | ~50 | PARTIAL | Yes (6.5) |
| 7. Bytecode/VM | ~30 | TODO | No |
| 8. Pipeline Integration | ~20 | PARTIAL | No |
| 9. Standard Library | ~40 | TODO | No |
| 10. Tooling | ~30 | TODO | No |
| 11. Benchmarks | ~25 | TODO | No |
| 12. Security | ~20 | PARTIAL | Yes (12.4) |
| 13. Formal Verification | ~15 | PARTIAL (22 Admitted) | No |
| 14. Property-Based | ~15 | TODO | No |
| 15. Regression | ~10 | TODO | No |
| 16. Cross-Platform | ~10 | TODO | No |
| 17. Documentation | ~10 | TODO | No |
| **TOTAL** | **~535** | **~15% covered** | **5 phases need superfuzzer** |

The superfuzzer is essential for phases 1.3, 2.4, 3.5, 6.5, and 12.4 — these are
where random/adversarial input testing catches the bugs that structured tests miss.
Without it, you can never be confident the compiler won't crash on unexpected input.
Everything else can be done with deterministic, hand-written tests.
