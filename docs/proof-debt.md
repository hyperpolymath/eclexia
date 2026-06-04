<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Proof debt

Ledger of soundness-relevant escape hatches in this repository's
proof-bearing code, per the estate
[Trusted-Base Reduction Policy](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc).

Scope of this repo's trusted base:

- **Coq** (`formal/coq/`) — `Typing.v` (Progress, Preservation, Soundness,
  Dimensional Safety) and `Echo.v` (echo-type soundness) are **fully
  constructive, axiom-free, 0 `Admitted`** — verified by `coqc 8.18.0`,
  `Print Assumptions` reports "Closed under the global context". They carry
  **no** entries here. The only escape hatches are the five linear-programming
  duality axioms in `ShadowPrices.v`, dispositioned below.
- **Agda** (`formal/agda/ResourceTracking.agda`) — no `postulate`s.
- **Rust** (`compiler/`, `runtime/`) — `unsafe` blocks exist only at FFI
  boundaries; none use `unsafePerformIO`/`unsafeCoerce`, so none are
  soundness-relevant under the policy's marker set.

> Note: `ShadowPrices.v` is **not** built by CI (it is commented out in
> `formal/coq/_CoqProject`); it is a standalone research artefact. Its axioms
> are therefore not on the path of any CI-verified theorem.

## (a) Discharged in this repo
- (none — entries are removed when the proof lands)

## (b) Budgeted — tested with refutation budget
- (none)

## (c) Necessary axiom

- `formal/coq/src/ShadowPrices.v:187` — `Axiom complementary_slackness`
  - **Justification**: complementary slackness for an optimal primal/dual
    pair. The standard constructive proof invokes strong duality, whose
    standard constructive proof in turn certifies the pivot via complementary
    slackness; the cycle is broken by axiomatising both (see
    `strong_duality`). Load-bearing for the shadow-price theorems.
  - **Citation**: Bertsimas & Tsitsiklis, *Introduction to Linear
    Optimization* (1997), §4.

- `formal/coq/src/ShadowPrices.v:215` — `Axiom lp_sensitivity`
  - **Justification**: the optimal value's sensitivity to the right-hand side
    equals the dual optimum (the shadow price), with a Lipschitz bound from
    `‖λ*‖₁`. Establishing the piecewise-linear / Lipschitz structure of the
    value function is not derivable from Coq's standard library.
  - **Citation**: requires Coquelicot real analysis or Mathlib4
    `LinearProgramming.duality.sensitivity`; Bertsimas & Tsitsiklis §5.

- `formal/coq/src/ShadowPrices.v:246` — `Axiom strong_duality`
  - **Justification**: strong LP duality (equal primal/dual optima). The
    constructive proof needs the LP fundamental theorem and matrix-rank
    infrastructure beyond what this file formalises.
  - **Citation**: Bertsimas & Tsitsiklis, *Introduction to Linear
    Optimization* (1997), Theorem 4.4.

## (d) DEBT — actively to be closed

- `formal/coq/src/ShadowPrices.v:161` — `Axiom weak_duality`
  - **Owner**: @hyperpolymath
  - **Plan**: dischargeable without external infrastructure — it reduces to
    list-level dot-product associativity and the transpose identity
    `(Aᵀλ)ᵀx = λᵀ(Ax)` over `lp_constraints`. Prove those two list lemmas and
    promote this to category (a).
  - **Deadline**: INDEFINITE — low priority; `ShadowPrices.v` is not on any
    CI-verified path.

- `formal/coq/src/ShadowPrices.v:519` — `Axiom dual_simplex_converges_to_optimal`
  - **Owner**: @hyperpolymath
  - **Plan**: requires a formalised pivot step, finite basis enumeration, and
    Bland's-rule cycle prevention — none defined in this file. The axiom is
    **not used** by any current theorem; it documents intended future work and
    could alternatively be deleted until that work begins.
  - **Deadline**: INDEFINITE — dependent on a formalised simplex kernel.
