;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; ANCHOR.scm — eclexia (authoritative upstream)

(define-module (eclexia anchor)
  #:export (anchor satellite-policy semantic-authority))

(define anchor
  '((schema . "hyperpolymath.anchor/1")
    (repo . "hyperpolymath/eclexia")
    (date . "2026-01-01")
    (authority . "upstream-canonical")
    (realignments
      . (((date . "2026-06-13")
          (what . "Echo (structured information loss) became core")
          (detail
            . "Echo[A,B] type former + echo/echo_witness/echo_base builtins joined the type system; landauer_cost(states,T):Resource[Energy] priced fibre erasure into the shadow-price economy (reversible retention = zero cost, Bennett; irreversible erasure = k_B*T*ln N, Landauer); Coq Echo.v soundness (A ≃ Σ(y:B). Echo f y) + axiom-free EchoThermo.v; THEORY.md §5.5 (graded comonad of structured loss). Echo is no longer peripheral — it is part of the language's identity.")
          (refs . ("eclexia#32" "THEORY.md §5.5" "formal/coq/src/Echo.v" "formal/coq/src/EchoThermo.v")))))
    (purpose
      . ("Define authoritative Eclexia language semantics and specification."
         "Maintain canonical compiler implementation."
         "Govern satellite repositories through anchor policy."))

    (identity
      . ((project . "Eclexia")
         (kind . "language")
         (one-sentence . "Energy-aware programming language with dimensional types, shadow-price optimization, and first-class structured information loss (Echo).")
         (domain . "sustainable-computing")))

    (semantic-authority
      . ((policy . "canonical")
         (owns
           . ("Language semantics and formal specification"
              "Type system and dimensional analysis rules"
              "Structured-loss semantics: the Echo[A,B] type former and its Landauer resource pricing (landauer_cost)"
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

    ;; mandatory-files updated 2026-06-13: the 6a2 metadata migrated from
    ;; root .scm to .machine_readable/6a2/*.a2ml (STATE.a2ml header: "converted
    ;; from scheme — 2026-04-11"). The old ./*.scm paths and ./.machine_read/
    ;; (sic) no longer exist.
    (mandatory-files
      . ("./ANCHOR.scm"
         "./.machine_readable/6a2/STATE.a2ml"
         "./.machine_readable/6a2/META.a2ml"
         "./.machine_readable/6a2/ECOSYSTEM.a2ml"
         "./.machine_readable/6a2/0-AI-MANIFEST.a2ml"))

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
