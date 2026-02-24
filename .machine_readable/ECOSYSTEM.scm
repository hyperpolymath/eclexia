;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem position for eclexia
;; Media-Type: application/vnd.ecosystem+scm

(ecosystem
  (version "1.0")
  (name "eclexia")
  (type "programming-language")
  (purpose "Economics-as-Code: resource-aware adaptive computation with shadow prices")

  (position-in-ecosystem
    (category "programming-languages")
    (subcategory "resource-aware-computation")
    (unique-value
      ("first-class resource tracking with dimensional analysis"
       "adaptive function selection under resource constraints"
       "shadow price computation for economic optimization"
       "carbon-aware scheduling built into the language")))

  (related-projects
    (sibling-standard
      ("panic-attacker" "security scanning tool used for toolchain hardening")
      ("verisimdb" "vulnerability similarity database")
      ("hypatia" "neurosymbolic CI/CD intelligence"))
    (potential-consumer
      ("gitbot-fleet" "bot orchestration using eclexia for resource-aware automation")
      ("ambientops" "ambient computing with eclexia resource tracking"))
    (inspiration
      ("rust" "ownership and type system")
      ("linear-haskell" "linear types and resource tracking")
      ("idris2" "dependent types and formal verification")))

  (what-this-is
    ("a programming language with economics-as-code primitives"
     "a compiler toolchain: lexer, parser, HIR, MIR, bytecode, VM"
     "a developer toolkit: LSP, formatter, linter, debugger, package manager"
     "a research vehicle for resource-aware computation"))

  (what-this-is-not
    ("a general-purpose systems language (use Rust instead)"
     "a web framework (it compiles to bytecode, not to JS)"
     "a replacement for established languages in their domains")))
