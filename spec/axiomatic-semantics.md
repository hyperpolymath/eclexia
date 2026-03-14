# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Eclexia Axiomatic Semantics: Resource Hoare Triples

**Version:** 1.0.0
**Date:** 2026-03-14

---

## 1. Overview

Eclexia's axiomatic semantics extend classical Hoare logic with resource
tracking. A *resource Hoare triple* has the form:

```
{P, R} S {Q, R'}
```

where:
- `P` — precondition on program state
- `R` — resource budget before execution
- `S` — statement or expression
- `Q` — postcondition on program state
- `R'` — resource budget after execution

The resource component `R` is a vector:

```
R = ⟨energy: ℝ≥0, carbon: ℝ≥0, latency: ℝ≥0, memory: ℝ≥0⟩
```

---

## 2. Resource Axioms

### 2.1 Resource Consumption

```
    @requires energy: E, carbon: C
    ──────────────────────────────────────────────────────────  [R-Consume]
    {P, R} f(args) {Q, R - ⟨E, C, 0, 0⟩}
    where R.energy ≥ E ∧ R.carbon ≥ C
```

### 2.2 Resource Monotonicity

```
    {P, R} S {Q, R'}
    ────────────────────  [R-Mono]
    R' ≤ R               (component-wise: resources only decrease)
```

### 2.3 Shadow Price Monotonicity

```
    R.energy_used / R.energy_budget = s₁
    R'.energy_used / R'.energy_budget = s₂
    s₁ ≤ s₂
    ──────────────────────────────────────────────────  [R-Shadow-Mono]
    shadow_price(R, energy) ≤ shadow_price(R', energy)
    (proved in formal/coq/src/ShadowPrices.v)
```

### 2.4 Budget Exhaustion

```
    R.energy < E     f @requires energy: E
    ──────────────────────────────────────────────  [R-Exhausted]
    {P, R} f(args) {⊥}     (execution fails with resource violation)
```

---

## 3. Adaptive Function Axioms

### 3.1 Solution Feasibility

```
    ∀sol ∈ solutions:
      sol.requires ≤ R ⟹ feasible(sol)
    ∃sol: feasible(sol)
    ──────────────────────────────────────────────────────  [A-Feasible]
    {P, R} adaptive f(args) {Q, R'}
    where R' = R - sol_best.cost
```

### 3.2 Solution Optimality

```
    sol_best = argmin_{sol ∈ feasible}(
      shadow_energy × sol.energy + shadow_latency × sol.latency + shadow_carbon × sol.carbon
    )
    ──────────────────────────────────────────────────────────  [A-Optimal]
    The selected solution minimises weighted resource cost
```

### 3.3 No Feasible Solution

```
    ∀sol ∈ solutions: ¬feasible(sol)
    ──────────────────────────────────────────  [A-NoSolution]
    {P, R} adaptive f(args) {⊥}
```

---

## 4. Classical Hoare Logic Rules

### 4.1 Assignment

```
    ──────────────────────────────────  [H-Assign]
    {Q[x ↦ e], R} x = e {Q, R}
```

### 4.2 Sequence

```
    {P, R} S₁ {Q, R'}     {Q, R'} S₂ {T, R''}
    ──────────────────────────────────────────────  [H-Seq]
    {P, R} S₁; S₂ {T, R''}
```

### 4.3 Conditional

```
    {P ∧ B, R} S₁ {Q, R₁}     {P ∧ ¬B, R} S₂ {Q, R₂}
    ────────────────────────────────────────────────────────  [H-If]
    {P, R} if B { S₁ } else { S₂ } {Q, min(R₁, R₂)}
```

### 4.4 While Loop

```
    {I ∧ B, R} S {I, R'}     R' < R (strict decrease ensures termination)
    ────────────────────────────────────────────────────────────────────  [H-While]
    {I, R} while B { S } {I ∧ ¬B, R'}
```

The resource budget serves as a natural loop variant: since resources are
consumed at each iteration and bounded below by 0, loops with resource-
consuming bodies are guaranteed to terminate.

### 4.5 Function Call

```
    f : (τ₁, …, τₙ) → τᵣ     @requires energy: E
    {P, R} body_of_f {Q, R - ⟨E,0,0,0⟩}
    ──────────────────────────────────────────────  [H-Call]
    {P, R} f(a₁, …, aₙ) {Q, R - ⟨E,0,0,0⟩}
```

### 4.6 Consequence

```
    P' ⟹ P     {P, R} S {Q, R'}     Q ⟹ Q'     R'' ≤ R'
    ──────────────────────────────────────────────────────────  [H-Conseq]
    {P', R} S {Q', R''}
```

---

## 5. Dimensional Safety Axioms

### 5.1 Dimensional Addition

```
    {e₁ : Resource(P, D), R}     {e₂ : Resource(P, D), R}
    ─────────────────────────────────────────────────────────  [D-Add]
    {e₁ + e₂ : Resource(P, D), R}     (same dimension preserved)
```

### 5.2 Dimensional Multiplication

```
    {e₁ : Resource(P, D₁), R}     {e₂ : Resource(P, D₂), R}
    ──────────────────────────────────────────────────────────  [D-Mul]
    {e₁ * e₂ : Resource(P, D₁ · D₂), R}     (dimensions compose)
```

### 5.3 Dimensional Mismatch

```
    D₁ ≠ D₂     attempt e₁ + e₂
    ──────────────────────────────────────────  [D-Mismatch]
    {⊥}     (type error: cannot add incompatible dimensions)
```

---

## 6. Key Theorems

### 6.1 Resource Safety

**Theorem:** If `{P, R} S {Q, R'}` is derivable and R has sufficient budget,
then S will not fail with a resource violation.

### 6.2 Budget Soundness

**Theorem:** The total resource consumption of a program is bounded by the
initial budget. Formally: if `{true, R₀} program {_, R_final}`, then
`R₀ - R_final ≥ 0` (component-wise).

### 6.3 Shadow Price Correctness

**Theorem:** The shadow price of resource `i` equals the marginal value of
relaxing constraint `i` by one unit. (Proved in `formal/coq/src/ShadowPrices.v`.)

### 6.4 Adaptive Pareto Optimality

**Theorem:** The selected adaptive solution is Pareto-optimal among feasible
alternatives with respect to the shadow-price-weighted cost function.
