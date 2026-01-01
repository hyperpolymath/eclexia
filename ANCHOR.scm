;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; ANCHOR.scm — eclexia (authoritative upstream)

(define-module (eclexia anchor)
  #:export (anchor satellite-policy semantic-authority))

(define anchor
  '((schema . "hyperpolymath.anchor/1")
    (repo . "hyperpolymath/eclexia")
    (date . "2026-01-01")
    (authority . "upstream-canonical")
    (purpose
      . ("Define authoritative Eclexia language semantics and specification."
         "Maintain canonical compiler implementation."
         "Govern satellite repositories through anchor policy."))

    (identity
      . ((project . "Eclexia")
         (kind . "language")
         (one-sentence . "Energy-aware programming language with dimensional types and shadow price optimization.")
         (domain . "sustainable-computing")))

    (semantic-authority
      . ((policy . "canonical")
         (owns
           . ("Language semantics and formal specification"
              "Type system and dimensional analysis rules"
              "Shadow price model and optimization algorithms"
              "Compiler implementation (lexer, parser, AST, type-checker, codegen)"
              "Runtime semantics and energy accounting"))
         (delegates
           . ((playgrounds . "Demos, benchmarks, visualization—not semantics")
              (bindings . "FFI wrappers for specific platforms")
              (tooling . "IDE plugins, formatters, linters")))))

    (implementation-policy
      . ((allowed
           . ("Rust" "OCaml"
              "Scheme" "Guile"
              "Shell" "Just"
              "Deno" "ReScript"
              "Markdown" "AsciiDoc"))
         (compiler-languages
           . ("Rust" "OCaml"))
         (forbidden
           . ("TypeScript" "Node.js" "npm" "Go"
              "Python (except SaltStack)"
              "Network-required compilation"))))

    (golden-path
      . ((smoke-test-command
           . ("cargo test"
              "cargo run -- check examples/"
              "cargo run -- run examples/fibonacci.ecl"))
         (success-criteria
           . ("All tests pass."
              "Compiler can parse and type-check example programs."
              "Interpreter executes with shadow price selection."))))

    (satellite-repos
      . ((eclexia-playground
           . ((purpose . "Experimentation sandbox, demos, benchmarks")
              (authority . "downstream")
              (semantic-policy . "illustrate-not-define")
              (anchor-ref . "hyperpolymath/eclexia-playground")))
         (eclexia-vscode
           . ((purpose . "VS Code language extension")
              (authority . "downstream")
              (semantic-policy . "consume-only")
              (anchor-ref . "hyperpolymath/eclexia-vscode")))
         (eclexia-docs
           . ((purpose . "User documentation and tutorials")
              (authority . "downstream")
              (semantic-policy . "document-not-define")
              (anchor-ref . "hyperpolymath/eclexia-docs")))))

    (mandatory-files
      . ("./ANCHOR.scm"
         "./META.scm"
         "./STATE.scm"
         "./ECOSYSTEM.scm"
         "./.machine_read/LLM_SUPERINTENDENT.scm"))

    (rsr . ((target-tier . "gold")
            (current-tier . "silver")
            (upgrade-path . "CI hardening + full coverage + release automation")))))

(define satellite-policy
  '((requirements
      . ((must-pin-upstream . #t)
         (must-declare-authority . #t)
         (must-have-anchor . #t)
         (must-have-golden-path . #t)))
    (semantic-policies
      . ((downstream . "May implement, must not redefine semantics")
         (illustrate-not-define . "May demo/visualize, cannot change meaning")
         (consume-only . "Read-only access to language spec")
         (document-not-define . "Explain, do not alter")))))

(define semantic-authority
  '((language-spec . "SPECIFICATION.md")
    (formal-proofs . "PROOFS.md")
    (type-theory . "THEORY.md")
    (algorithms . "ALGORITHMS.md")))
