;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; LLM_SUPERINTENDENT.scm — Machine-readable guidance for AI assistants

(define-module (eclexia machine-read llm-superintendent)
  #:export (superintendent-policy repo-identity constraints directives))

(define superintendent-policy
  '((schema . "hyperpolymath.superintendent/1")
    (repo . "hyperpolymath/eclexia")
    (role . "upstream-canonical")
    (last-updated . "2026-01-01")))

(define repo-identity
  '((name . "Eclexia")
    (type . "programming-language")
    (domain . "sustainable-computing")
    (one-liner . "Energy-aware language with dimensional types and shadow price optimization")

    (core-concepts
      . ((dimensional-types . "Types carry physical units (joules, watts, seconds)")
         (shadow-prices . "Runtime cost model: energy + latency + carbon")
         (adaptive-execution . "Select implementation based on current shadow prices")
         (energy-accounting . "Track and report energy consumption at language level")))

    (this-repo-owns
      . ("Language semantics and specification"
         "Compiler implementation (Rust)"
         "Formal proofs and type theory"
         "Reference interpreter"
         "CLI and REPL"))

    (this-repo-does-not-own
      . ("Playground demos (see eclexia-playground)"
         "IDE extensions"
         "User tutorials beyond GETTING_STARTED.md"))))

(define constraints
  '((language-policy
      . ((allowed . ("Rust" "OCaml" "Scheme" "Shell" "Just" "Deno" "ReScript" "Markdown" "AsciiDoc"))
         (forbidden . ("TypeScript" "Node.js" "npm" "Go" "Python"))
         (compiler-only . ("Rust" "OCaml"))))

    (semantic-policy
      . ((authority . "This repo is the ONLY authoritative source for Eclexia semantics")
         (no-forks-defining-semantics . #t)
         (satellites-must-pin . #t)))

    (security-policy
      . ((no-md5-sha1 . #t)
         (https-only . #t)
         (no-hardcoded-secrets . #t)
         (spdx-headers-required . #t)))

    (rsr-compliance
      . ((target . "gold")
         (sha-pinned-actions . #t)
         (multi-platform-ci . #t)))))

(define directives
  '((when-modifying-compiler
      . ("Ensure all existing tests pass"
         "Add tests for new functionality"
         "Update SPECIFICATION.md if semantics change"
         "Update STATE.scm completion percentages"))

    (when-adding-features
      . ("Check alignment with energy-aware computing mission"
         "Consider shadow price implications"
         "Document in appropriate .md file"
         "Add examples in examples/ directory"))

    (when-working-on-satellites
      . ("Satellites CANNOT define or change language semantics"
         "Always pin to specific upstream commit"
         "Reference upstream ANCHOR.scm for policy"))

    (golden-path-verification
      . ("cargo test — must pass"
         "cargo run -- check examples/ — must succeed"
         "cargo run -- run examples/fibonacci.ecl — must execute"))))
