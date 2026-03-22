;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Meta-level information for eclexia
;; Media-Type: application/meta+scheme

(meta
  (architecture-decisions
    (adr-001
      (title "Stack-based bytecode VM over tree-walking interpreter")
      (status "accepted")
      (context "Need efficient execution for resource-tracking overhead")
      (decision "Compile to bytecode via MIR, execute on stack-based VM")
      (consequences "Better performance, more complex compilation pipeline"))
    (adr-002
      (title "Arena allocation for AST/HIR/MIR nodes")
      (status "accepted")
      (context "Compiler data structures need stable references during passes")
      (decision "Use la-arena for arena-allocated indices")
      (consequences "Cache-friendly, no lifetime issues, index-based references"))
    (adr-003
      (title "Shadow prices as first-class language construct")
      (status "accepted")
      (context "Economics-as-code requires runtime cost awareness")
      (decision "Shadow prices computed dynamically, accessible via language primitives")
      (consequences "Unique language feature, runtime overhead for tracking"))
    (adr-004
      (title "Adaptive functions with constraint-based selection")
      (status "accepted")
      (context "Multiple implementations with different resource profiles")
      (decision "Runtime selects optimal implementation based on current constraints")
      (consequences "Automatic optimization, requires resource budget specification"))
    (adr-005
      (title "Tower-LSP for language server")
      (status "accepted")
      (context "Need async LSP server with Rust ecosystem compatibility")
      (decision "Use tower-lsp with DashMap for concurrent document storage")
      (consequences "Production-quality LSP, async/await based")))

  (development-practices
    (code-style
      (language "Rust")
      (formatter "rustfmt")
      (linter "clippy")
      (security-scanner "panic-attack"))
    (security
      (principle "Defense in depth")
      (scanner "panic-attack assail")
      (target "Zero production weak points")
      (current-status "Achieved - zero weak points across all crates"))
    (testing
      (framework "cargo test")
      (categories "unit, conformance, property-based, integration")
      (lib-tests 62)
      (conformance-tests 51)
      (property-tests 11))
    (versioning "SemVer")
    (documentation "Markdown + AsciiDoc")
    (branching "main for stable")
    (ci "GitHub Actions with hypatia-scan"))

  (design-rationale
    (resource-aware-computation
      "Programs should be aware of their resource consumption"
      "Dimensional analysis prevents unit errors at compile time"
      "Carbon-aware scheduling enables environmentally conscious computing")
    (economics-as-code
      "Economic concepts (shadow prices, constraints, optimization) are language primitives"
      "Adaptive functions automatically select optimal implementations"
      "Resource budgets enforce consumption limits")))
