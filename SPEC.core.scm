;;; SPEC.core.scm — Eclexia Core Specification
;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;
;; This file defines the minimal resource lattice and evaluation semantics
;; for Eclexia's resource-aware computation model.

;;;; ============================================================
;;;; SECTION 1: RESOURCE LATTICE
;;;; ============================================================

;; The resource lattice defines the partial ordering of resource types
;; and their relationships. Resources are first-class values with
;; dimensional analysis at the type level.

(define resource-lattice
  '((name . "eclexia-resource-lattice")
    (version . "1.0.0")

    ;; Base resource dimensions (form an abelian group under multiplication)
    (base-dimensions
      . ((time . ((si-unit . "s")
                  (description . "Duration/latency")
                  (exponent . (time . 1))))
         (energy . ((si-unit . "J")
                    (description . "Energy consumption")
                    (exponent . (mass . 1) (length . 2) (time . -2))))
         (carbon . ((si-unit . "kgCO2e")
                    (description . "Carbon dioxide equivalent emissions")
                    (exponent . (carbon . 1))))
         (memory . ((si-unit . "bit")
                    (description . "Information/memory usage")
                    (exponent . (information . 1))))))

    ;; Derived dimensions (computed from base)
    (derived-dimensions
      . ((power . ((formula . "energy / time")
                   (si-unit . "W")
                   (exponent . (mass . 1) (length . 2) (time . -3))))
         (carbon-intensity . ((formula . "carbon / energy")
                              (si-unit . "gCO2e/kWh")
                              (description . "Grid carbon intensity")))))

    ;; Resource bounds form a partial order
    (bound-ordering
      . ((description . "Resource bounds form a meet-semilattice")
         (top . unbounded)          ;; No constraint
         (bottom . impossible)       ;; Unsatisfiable
         (meet . "min of bounds")    ;; Stricter constraint wins
         (join . "max of bounds")))  ;; Looser constraint

    ;; Constraint operators
    (constraint-operators
      . ((< . "less than bound")
         (<= . "at most bound")
         (= . "exactly bound")
         (>= . "at least (for provides)")
         (> . "greater than (for provides)")))))


;;;; ============================================================
;;;; SECTION 2: CORE TYPE SYSTEM
;;;; ============================================================

(define type-system
  '((name . "eclexia-type-system")
    (version . "1.0.0")

    ;; Primitive types
    (primitives
      . ((Unit . "The unit type, single value ()")
         (Bool . "Boolean: true | false")
         (Int . "Signed 64-bit integer")
         (Float . "IEEE 754 double precision")
         (String . "UTF-8 string")))

    ;; Resource-annotated types
    (resource-types
      . ((syntax . "T @requires: constraints @provides: guarantees")
         (example . "Int @requires: energy < 10J, latency < 100ms")
         (semantics . "Type carries resource contract")))

    ;; Dimensional types
    (dimensional-types
      . ((energy . "Energy = Float @dimension: J")
         (time . "Time = Float @dimension: s")
         (carbon . "Carbon = Float @dimension: kgCO2e")
         (power . "Power = Energy / Time")))

    ;; Type algebra
    (type-rules
      . ((dimensional-addition
           . "T @dim:D + T @dim:D → T @dim:D (dimensions must match)")
         (dimensional-multiplication
           . "T @dim:D1 * T @dim:D2 → T @dim:D1*D2")
         (dimensional-division
           . "T @dim:D1 / T @dim:D2 → T @dim:D1/D2")
         (resource-propagation
           . "Calling f @requires:R propagates R to caller")))))


;;;; ============================================================
;;;; SECTION 3: ADAPTIVE EVALUATION SEMANTICS
;;;; ============================================================

(define evaluation-semantics
  '((name . "eclexia-evaluation")
    (version . "1.0.0")

    ;; Evaluation context carries resource state
    (context
      . ((components
           . ((budget . "Remaining resource allowances")
              (shadow-prices . "Marginal values λ for each resource")
              (current-usage . "Accumulated resource consumption")
              (environment . "Variable bindings")))
         (notation . "Γ; B; λ; U ⊢ e ⇓ v; U'")))

    ;; Core evaluation rules
    (rules
      . (
         ;; Literals evaluate without resource cost
         (E-LIT
           . ((premise . "literal n")
              (conclusion . "Γ; B; λ; U ⊢ n ⇓ n; U")
              (note . "Literals consume no resources")))

         ;; Variables lookup in environment
         (E-VAR
           . ((premise . "x ∈ dom(Γ)")
              (conclusion . "Γ; B; λ; U ⊢ x ⇓ Γ(x); U")))

         ;; Binary operations check dimension compatibility
         (E-BINOP
           . ((premises
                . ("Γ; B; λ; U ⊢ e1 ⇓ v1; U1"
                   "Γ; B; λ; U1 ⊢ e2 ⇓ v2; U2"
                   "compatible-dims(op, dim(v1), dim(v2))"))
              (conclusion . "Γ; B; λ; U ⊢ e1 op e2 ⇓ apply-op(op, v1, v2); U2")))

         ;; Function application with resource tracking
         (E-APP
           . ((premises
                . ("Γ; B; λ; U ⊢ e ⇓ fn(x) body @R; U1"
                   "Γ; B; λ; U1 ⊢ arg ⇓ v; U2"
                   "Γ[x↦v]; B; λ; U2 ⊢ body ⇓ result; U3"
                   "satisfies(U3 - U, R)"))
              (conclusion . "Γ; B; λ; U ⊢ e(arg) ⇓ result; U3")))

         ;; Adaptive function: select solution by weighted cost
         (E-ADAPTIVE
           . ((premises
                . ("Γ; B; λ; U ⊢ e ⇓ adaptive fn solutions @R; U1"
                   "Γ; B; λ; U1 ⊢ args ⇓ vs; U2"
                   "S = select-solution(solutions, Γ, B, λ)"
                   "S ≠ ⊥"
                   "Γ[params↦vs]; B; λ; U2 ⊢ S.body ⇓ result; U3"
                   "satisfies(U3 - U2, S.provides)"))
              (conclusion . "Γ; B; λ; U ⊢ e(args) ⇓ result; U3")
              (note . "Solution selected by minimizing weighted cost")))

         ;; Constraint violation → deterministic error
         (E-VIOLATION
           . ((premises
                . ("Γ; B; λ; U ⊢ e ⇓ v; U'"
                   "¬ satisfies(U' - U, @requires R)"))
              (conclusion . "Γ; B; λ; U ⊢ e ⇓ ResourceViolation(R); U'")
              (note . "Deterministic failure, not exception")))))

    ;; Solution selection algorithm
    (solution-selection
      . ((algorithm . "weighted-cost-minimization")
         (formula . "cost(S) = Σ λ_r × S.provides[r]")
         (selection . "argmin_{S ∈ solutions} cost(S) where S.when = true")
         (tie-breaker . "first declared solution")
         (no-valid-solution . "ResourceViolation: no solution satisfies constraints")))

    ;; Shadow price semantics
    (shadow-prices
      . ((definition . "Marginal value of one additional unit of resource r")
         (interpretation
           . ("λ_energy = value of 1 more Joule"
              "λ_time = value of 1 more millisecond"
              "λ_carbon = value of 1 gram less CO2"))
         (initialization . "λ = (1.0, 1.0, 1.0) by default")
         (update-rule . "LP duality or gradient descent (runtime-dependent)")))))


;;;; ============================================================
;;;; SECTION 4: CONSTRAINT CHECKING
;;;; ============================================================

(define constraint-checking
  '((name . "eclexia-constraints")
    (version . "1.0.0")

    ;; Constraint syntax
    (constraint-forms
      . ((@requires . "Input constraint: must hold at entry")
         (@provides . "Output guarantee: will hold at exit")
         (@optimize . "Objective: minimize/maximize resource")
         (@when . "Guard condition for solution applicability")
         (@defer_until . "Delay execution until condition")))

    ;; Constraint validation rules
    (validation
      . ((at-call-site
           . "Check @requires against current budget B")
         (at-return
           . "Verify actual usage ≤ @provides")
         (static-check
           . "Type checker verifies dimensional compatibility")
         (dynamic-check
           . "Runtime tracks actual consumption")))

    ;; Violation behavior (deterministic)
    (violation-semantics
      . ((type . "ResourceViolation")
         (contents
           . ((resource . "Which resource exceeded")
              (constraint . "The violated constraint")
              (actual . "Actual usage value")
              (limit . "The bound that was exceeded")
              (location . "Source location of violation")))
         (behavior . "Deterministic error, not exception")
         (propagation . "Error propagates up call stack")
         (recovery . "No automatic recovery; caller must handle")))))


;;;; ============================================================
;;;; SECTION 5: CONFORMANCE REQUIREMENTS
;;;; ============================================================

(define conformance
  '((name . "eclexia-conformance")
    (version . "1.0.0")

    ;; Minimum viable implementation
    (minimum-requirements
      . ((resource-tracking
           . "Must track at least: time, energy")
         (constraint-checking
           . "Must reject @requires violations")
         (dimensional-analysis
           . "Must reject dimension mismatches at type check")
         (adaptive-selection
           . "Must select solution by weighted cost")
         (deterministic-errors
           . "Constraint violations must be deterministic")))

    ;; Test corpus categories
    (test-corpus
      . ((valid
           . ((description . "Programs that should succeed")
              (categories
                . ("resource-typed computation"
                   "adaptive function selection"
                   "dimensional arithmetic"
                   "constraint satisfaction"))))
         (invalid
           . ((description . "Programs that should fail deterministically")
              (categories
                . ("resource constraint violation"
                   "dimension mismatch"
                   "no valid solution available"
                   "budget exhaustion"))))))

    ;; Smoke test command
    (smoke-test
      . ((command . "cargo test && cargo run -- run examples/hello.ecl")
         (success-criteria
           . ("All unit tests pass"
              "hello.ecl runs without error"
              "Output includes: Hello, Economics-as-Code!"))))))


;;;; ============================================================
;;;; SECTION 6: REFERENCE
;;;; ============================================================

(define specification-metadata
  '((schema . "eclexia.spec/1.0")
    (date . "2026-01-01")
    (authority . "SPEC.core.scm is authoritative for semantics")
    (implementation . "compiler/ and runtime/ implement this spec")
    (related-docs
      . ("SPECIFICATION.md - full language specification"
         "PROOFS.md - formal correctness proofs"
         "THEORY.md - theoretical foundations"))))
