;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; SATELLITE_ANCHOR_TEMPLATE.scm — Template for downstream/satellite repositories
;;;
;;; USAGE: Copy this file to your satellite repo as ANCHOR.scm and customize
;;;        the fields marked with TODO comments.

(define-module (eclexia-satellite anchor)
  #:export (anchor))

(define anchor
  '((schema . "hyperpolymath.anchor/1")
    ;; TODO: Set your satellite repo name
    (repo . "hyperpolymath/eclexia-SATELLITE_NAME")
    ;; TODO: Set current date
    (date . "YYYY-MM-DD")
    (authority . "repo-superintendent")
    ;; TODO: Define your satellite's purpose (scope arrest)
    (purpose
      . ("Scope arrest: [DESCRIBE BOUNDARIES]"
         "Keep one reproducible, offline golden path."
         "Ensure satellite stays aligned with upstream Eclexia language identity/spec."))

    (identity
      . ((project . "Eclexia [SATELLITE_NAME]")
         ;; TODO: Set kind (playground, tooling, bindings, docs, etc.)
         (kind . "[playground|tooling|bindings|docs]")
         ;; TODO: One-sentence description
         (one-sentence . "[DESCRIBE YOUR SATELLITE]")
         (upstream . "hyperpolymath/eclexia")))

    (semantic-anchor
      . ((policy . "downstream")
         (upstream-authority
           . ("Language semantics/spec live in hyperpolymath/eclexia."
              "This repo may illustrate, prototype, benchmark, or visualize—but not define semantics."))))

    ;; TODO: Customize allowed/quarantined/forbidden based on satellite purpose
    (implementation-policy
      . ((allowed
           . ("Scheme" "Shell" "Just"
              "Deno" "ReScript"
              ;; Add other languages appropriate for your satellite
              "Markdown" "AsciiDoc"))
         (quarantined
           . ("Any 'compiler' work (must live upstream unless explicitly delegated by upstream ANCHOR)"
              "Any new runtime/backends beyond demo stubs"))
         (forbidden
           . ("Second authoritative compiler"
              "Changing Eclexia's mission statement in this repo"
              "Network-required execution for demos"))))

    ;; TODO: Define your golden path smoke tests
    (golden-path
      . ((smoke-test-command
           . ("just --list"
              "just test  ;; must exist"
              "just demo  ;; must exist; runs one canonical example offline"))
         (success-criteria
           . ("A clean checkout can run `just demo` offline."
              "[ADD SATELLITE-SPECIFIC SUCCESS CRITERIA]"
              "README/STATE do not contradict upstream identity."))))

    ;; TODO: List mandatory machine-readable files for your satellite
    (mandatory-files
      . ("./.machine_read/LLM_SUPERINTENDENT.scm"
         "./.machine_read/ROADMAP.f0.scm"))

    ;; TODO: Define first-pass setup directives
    (first-pass-directives
      . ("[ADD SETUP DIRECTIVES]"
         "Pin upstream commits if importing artifacts; document the pin."))

    ;; RSR compliance tier
    (rsr . ((target-tier . "bronze-now")
            (upgrade-path . "silver-after-f1 (CI + pinned artifacts + e2e demo)")))))


;;; ============================================================================
;;; EXAMPLE: eclexia-playground ANCHOR
;;; ============================================================================
;;; Below is a complete example for the eclexia-playground satellite.
;;; Delete this section after customizing the template above.

(define example-playground-anchor
  '((schema . "hyperpolymath.anchor/1")
    (repo . "hyperpolymath/eclexia-playground")
    (date . "2026-01-01")
    (authority . "repo-superintendent")
    (purpose
      . ("Scope arrest: sandbox + demos only. No second authoritative implementation."
         "Keep one reproducible, offline golden path."
         "Ensure satellite stays aligned with upstream Eclexia language identity/spec."))

    (identity
      . ((project . "Eclexia Playground")
         (kind . "playground")
         (one-sentence . "Experimentation sandbox for Eclexia (sustainable computing / energy-aware language ideas).")
         (upstream . "hyperpolymath/eclexia")))

    (semantic-anchor
      . ((policy . "downstream")
         (upstream-authority
           . ("Language semantics/spec live in hyperpolymath/eclexia."
              "This repo may illustrate, prototype, benchmark, or visualize—but not define semantics."))))

    (implementation-policy
      . ((allowed
           . ("Scheme" "Shell" "Just"
              "Deno" "ReScript"
              "Zig" "V"
              "Markdown" "AsciiDoc"))
         (quarantined
           . ("Any 'compiler' work (must live upstream unless explicitly delegated by upstream ANCHOR)"
              "Any new runtime/backends beyond demo stubs"))
         (forbidden
           . ("Second authoritative compiler"
              "Changing Eclexia's mission statement in this repo"
              "Network-required execution for demos"))))

    (golden-path
      . ((smoke-test-command
           . ("just --list"
              "just test  ;; must exist; may call deno test or scheme harness"
              "just demo  ;; must exist; runs one canonical example offline"))
         (success-criteria
           . ("A clean checkout can run `just demo` offline."
              "At least 1 example demonstrates the *intended* Eclexia concept (energy/cost annotations) in a testable way."
              "README/STATE do not contradict upstream identity."))))

    (mandatory-files
      . ("./.machine_read/LLM_SUPERINTENDENT.scm"
         "./.machine_read/ROADMAP.f0.scm"
         "./.machine_read/SPEC.playground.scm"))

    (first-pass-directives
      . ("Add SPEC.playground.scm that defines: demo contract, artifact contract, and upstream pin."
         "If README claims a tech split (e.g., Zig/V), make it explicitly 'demo scaffolding', not semantics."
         "Pin upstream commits if importing artifacts; document the pin."))

    (rsr . ((target-tier . "bronze-now")
            (upgrade-path . "silver-after-f1 (CI + pinned artifacts + e2e demo)")))))
