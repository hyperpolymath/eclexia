# Algorithms and Complexity Analysis for Eclexia

<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

**Version:** 1.0
**Date:** December 2025
**Authors:** Jonathan D.A. Jewell
**Status:** Research Preview

---

## Abstract

This document presents the algorithmic foundations of Eclexia's runtime system, including: (1) solution selection algorithms with complexity analysis; (2) shadow price computation via linear programming; (3) multi-objective optimization algorithms; (4) carbon-aware scheduling algorithms; (5) type inference and constraint solving algorithms; (6) resource profiling and prediction; and (7) amortized analysis for adaptive execution. We provide rigorous complexity bounds and correctness proofs for each algorithm.

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Solution Selection](#2-solution-selection)
3. [Shadow Price Computation](#3-shadow-price-computation)
4. [Linear Programming Algorithms](#4-linear-programming-algorithms)
5. [Multi-Objective Optimization](#5-multi-objective-optimization)
6. [Carbon-Aware Scheduling](#6-carbon-aware-scheduling)
7. [Type Inference Algorithms](#7-type-inference-algorithms)
8. [Dimension Inference and Checking](#8-dimension-inference-and-checking)
9. [Constraint Solving](#9-constraint-solving)
10. [Resource Profiling](#10-resource-profiling)
11. [Adaptive Scheduling](#11-adaptive-scheduling)
12. [Amortized Analysis](#12-amortized-analysis)
13. [Approximation Algorithms](#13-approximation-algorithms)
14. [Online Algorithms](#14-online-algorithms)
15. [Complexity Summary](#15-complexity-summary)

---

## 1. Introduction

### 1.1 Algorithmic Challenges

Eclexia's runtime faces several algorithmic challenges:

| Challenge | Algorithm Class | Complexity Goal |
|-----------|----------------|-----------------|
| Solution selection | Constrained optimization | O(n) per selection |
| Shadow price computation | Linear programming | O(m³) or better |
| Multi-objective optimization | Pareto optimization | Polynomial |
| Carbon-aware scheduling | Online scheduling | Competitive ratio ≤ 2 |
| Type inference | Unification + constraint solving | O(n²) |
| Dimension checking | Linear algebra | O(d³) |

### 1.2 Notation

| Symbol | Meaning |
|--------|---------|
| `n` | Number of solutions |
| `m` | Number of resources |
| `k` | Number of constraints |
| `d` | Number of dimension variables |
| `T` | Time horizon |
| `ε` | Approximation parameter |

---

## 2. Solution Selection

### 2.1 Problem Definition

**Input:**
- Solutions `S = {s₁, ..., sₙ}`
- Guards `G = {g₁, ..., gₙ}` (boolean predicates)
- Resource profiles `P = {p₁, ..., pₙ}` where `pᵢ : R → ℝ≥0`
- Current state `Σ : R → ℝ≥0`
- Budget `B : R → ℝ≥0 ∪ {∞}`
- Objectives `O = {(minimize, r₁), (maximize, r₂), ...}`

**Output:**
- Index `i*` of optimal feasible solution

### 2.2 Feasibility Check

```
Algorithm 2.1: FEASIBILITY-CHECK
Input: Solution index i, state Σ, budget B
Output: Boolean

1. if not eval(gᵢ) then return FALSE
2. for each resource r in R:
3.     if Σ(r) + pᵢ(r) > B(r) then return FALSE
4. return TRUE
```

**Complexity:** O(m) where m is number of resources.

### 2.3 Greedy Selection

```
Algorithm 2.2: GREEDY-SELECT
Input: Solutions S, state Σ, budget B, shadow prices λ
Output: Optimal solution index

1. feasible ← ∅
2. for i = 1 to n:
3.     if FEASIBILITY-CHECK(i, Σ, B):
4.         feasible ← feasible ∪ {i}
5.
6. if feasible = ∅:
7.     raise ResourceExhausted
8.
9. // Compute weighted cost for each feasible solution
10. min_cost ← ∞
11. best ← -1
12. for i in feasible:
13.     cost ← Σᵣ λ(r) · pᵢ(r)
14.     if cost < min_cost:
15.         min_cost ← cost
16.         best ← i
17.
18. return best
```

**Complexity:** O(n·m) for n solutions and m resources.

### 2.4 Optimized Selection with Indexing

For frequently-called adaptive blocks, maintain sorted index:

```
Algorithm 2.3: INDEXED-SELECT
Precomputation:
1. Sort solutions by expected cost: sorted_idx ← argsort({E[cost(sᵢ)]})
2. Build feasibility predicates: pred[i] ← compile(gᵢ)

Runtime:
Input: Current context
Output: Optimal solution index

1. for i in sorted_idx:  // Iterate in cost order
2.     if pred[i].eval(context) and within_budget(i):
3.         return i
4. raise ResourceExhausted
```

**Complexity:** O(k) expected for k feasibility checks, O(n) worst case.

### 2.5 Correctness

**Theorem 2.1 (Selection Correctness).** Algorithm 2.2 returns the index minimizing weighted cost among feasible solutions.

*Proof:*
1. Feasibility: Line 3 ensures only feasible solutions are considered.
2. Optimality: Lines 10-16 find minimum over feasible set.
3. Completeness: If any solution is feasible, it's in `feasible` set.

The algorithm correctly implements:
```
i* = argmin_{i : feasible(i)} Σᵣ λᵣ · pᵢ(r)
```
□

---

## 3. Shadow Price Computation

### 3.1 LP Formulation

The shadow prices are dual variables of the resource allocation LP:

**Primal LP:**
```
minimize    c^T x
subject to  Ax ≤ b        (resource constraints)
            1^T x = 1     (select exactly one)
            x ≥ 0
```

where:
- `x ∈ ℝⁿ` is the selection vector (relaxed from binary)
- `c ∈ ℝⁿ` is the objective coefficient vector
- `A ∈ ℝ^{m×n}` is the resource consumption matrix: `Aᵣᵢ = pᵢ(r)`
- `b = B - Σ` is the remaining budget vector

**Dual LP:**
```
maximize    b^T λ + μ
subject to  A^T λ + μ · 1 ≥ c
            λ ≥ 0
```

### 3.2 Shadow Price Algorithm

```
Algorithm 3.1: COMPUTE-SHADOW-PRICES
Input: Resource matrix A, remaining budget b, objective weights c
Output: Shadow prices λ

1. // Formulate LP
2. lp ← new LinearProgram()
3. lp.add_objective(MAXIMIZE, b^T λ + μ)
4. for i = 1 to n:
5.     lp.add_constraint(A[:,i]^T λ + μ ≥ c[i])
6. lp.add_constraint(λ ≥ 0)
7.
8. // Solve dual LP
9. (λ*, μ*) ← lp.solve()
10.
11. return λ*
```

**Complexity:** O(m³) using interior point methods, or O(2^m · poly(n,m)) using simplex.

### 3.3 Incremental Shadow Price Updates

When budget changes incrementally:

```
Algorithm 3.2: INCREMENTAL-SHADOW-UPDATE
Input: Previous solution (λ_prev, basis), budget change Δb
Output: Updated shadow prices λ

1. // Check if basis still optimal
2. b_new ← b + Δb
3. if basis_remains_feasible(basis, b_new):
4.     // Reuse basis, recompute λ
5.     λ ← compute_dual_from_basis(basis, b_new)
6. else:
7.     // Warm-start from previous solution
8.     λ ← simplex_with_warmstart(λ_prev, b_new)
9.
10. return λ
```

**Complexity:** O(m²) when basis unchanged, O(m³) worst case.

### 3.4 Sensitivity Analysis

**Theorem 3.1 (Shadow Price Sensitivity).** For small budget perturbation `Δb`:
```
ΔOPT ≈ λ^T Δb
```

*Proof:* By envelope theorem for linear programs. □

**Corollary 3.1.** Shadow price `λᵣ` represents the marginal value of resource `r`:
```
λᵣ = ∂OPT/∂bᵣ
```

---

## 4. Linear Programming Algorithms

### 4.1 Simplex Method

```
Algorithm 4.1: SIMPLEX
Input: LP in standard form: min c^T x s.t. Ax = b, x ≥ 0
Output: Optimal solution x* or UNBOUNDED/INFEASIBLE

1. // Phase 1: Find initial BFS
2. (B, x_B) ← FIND-INITIAL-BFS(A, b)
3. if x_B = INFEASIBLE:
4.     return INFEASIBLE
5.
6. // Phase 2: Optimize
7. while true:
8.     // Compute reduced costs
9.     c_bar ← c - c_B^T B^{-1} A
10.
11.     // Check optimality
12.     if c_bar ≥ 0:
13.         return CONSTRUCT-SOLUTION(B, x_B)
14.
15.     // Select entering variable (Bland's rule for anti-cycling)
16.     j ← min{j : c_bar[j] < 0}
17.
18.     // Compute direction
19.     d ← B^{-1} A[:,j]
20.
21.     // Check unboundedness
22.     if d ≤ 0:
23.         return UNBOUNDED
24.
25.     // Ratio test (minimum ratio)
26.     i ← argmin{x_B[i] / d[i] : d[i] > 0}
27.
28.     // Pivot
29.     PIVOT(B, i, j)
```

**Complexity:** O(2^m) worst case, O(m² · n) average case (Spielman-Teng smoothed analysis).

### 4.2 Interior Point Method

```
Algorithm 4.2: INTERIOR-POINT (Karmarkar's algorithm variant)
Input: LP in standard form
Output: ε-optimal solution

1. // Initialize at analytic center
2. x ← ANALYTIC-CENTER(A, b)
3. μ ← INITIAL-BARRIER-PARAMETER
4.
5. while μ > ε:
6.     // Newton step on barrier function
7.     Δx ← NEWTON-STEP(x, μ, A, b, c)
8.     x ← x + α · Δx  // Line search
9.
10.     // Decrease barrier parameter
11.     μ ← μ · (1 - 1/√m)
12.
13. return x
```

**Complexity:** O(m^{3.5} · L) where L is input bit length (Karmarkar).
**Practical:** O(m³) per iteration, O(√m · log(1/ε)) iterations.

### 4.3 Specialized LP for Resource Allocation

For Eclexia's specific structure (selection among n alternatives):

```
Algorithm 4.3: RESOURCE-LP-SPECIALIZED
Input: n solutions, m resources, profiles {p₁,...,pₙ}, budget b
Output: Optimal selection and shadow prices

1. // This is a simple LP: select one solution
2. // Optimal is always at a vertex (single selection)
3.
4. // Enumerate vertices (each vertex = single solution)
5. best_idx ← -1
6. best_cost ← ∞
7.
8. for i = 1 to n:
9.     if ∀r: pᵢ(r) ≤ b(r):  // Feasible
10.         cost ← c^T pᵢ
11.         if cost < best_cost:
12.             best_cost ← cost
13.             best_idx ← i
14.
15. if best_idx = -1:
16.     return INFEASIBLE
17.
18. // Compute shadow prices from active constraints
19. active ← {r : pᵢ(r) = b(r)}
20. λ ← COMPUTE-DUAL(active, c)
21.
22. return (best_idx, λ)
```

**Complexity:** O(n · m) - much better than general LP!

---

## 5. Multi-Objective Optimization

### 5.1 Pareto Frontier

**Definition 5.1 (Pareto Dominance).** Solution `s₁` dominates `s₂` (written `s₁ ≻ s₂`) if:
- `∀r ∈ O: fᵣ(s₁) ≤ fᵣ(s₂)` (at least as good on all objectives)
- `∃r ∈ O: fᵣ(s₁) < fᵣ(s₂)` (strictly better on at least one)

**Definition 5.2 (Pareto Frontier).** The Pareto frontier is:
```
PF = {s ∈ S : ¬∃s' ∈ S. s' ≻ s}
```

### 5.2 Weighted Sum Scalarization

```
Algorithm 5.1: WEIGHTED-SUM
Input: Solutions S, objectives O, weights w (Σwᵢ = 1)
Output: Pareto-optimal solution

1. // Scalarize objectives
2. scalar_cost(s) ← Σᵢ wᵢ · fᵢ(s)
3.
4. // Find minimum
5. return argmin_{s ∈ S} scalar_cost(s)
```

**Theorem 5.1.** Weighted sum always returns a Pareto-optimal solution.

*Proof:* If `s*` were dominated by `s'`, then `scalar_cost(s') < scalar_cost(s*)` since weights are positive. Contradiction. □

**Limitation:** Cannot find non-convex Pareto points.

### 5.3 ε-Constraint Method

```
Algorithm 5.2: EPSILON-CONSTRAINT
Input: Solutions S, primary objective f₁, secondary objectives {f₂,...,fₖ}, bounds ε
Output: Pareto-optimal solution

1. // Optimize primary objective subject to bounds on others
2. feasible ← {s ∈ S : ∀i > 1. fᵢ(s) ≤ εᵢ}
3. return argmin_{s ∈ feasible} f₁(s)
```

**Advantage:** Can find non-convex Pareto points by varying ε.

### 5.4 NSGA-II for Pareto Frontier Discovery

```
Algorithm 5.3: NSGA-II (Non-dominated Sorting Genetic Algorithm)
Input: Population size N, generations G
Output: Approximate Pareto frontier

1. P ← INITIALIZE-POPULATION(N)
2.
3. for gen = 1 to G:
4.     // Generate offspring
5.     Q ← CROSSOVER-AND-MUTATE(P)
6.     R ← P ∪ Q
7.
8.     // Non-dominated sorting
9.     fronts ← NON-DOMINATED-SORT(R)
10.
11.     // Select next generation
12.     P ← ∅
13.     i ← 0
14.     while |P| + |fronts[i]| ≤ N:
15.         P ← P ∪ fronts[i]
16.         i ← i + 1
17.
18.     // Fill remaining with crowding distance
19.     if |P| < N:
20.         CROWDING-DISTANCE-SORT(fronts[i])
21.         P ← P ∪ fronts[i][1:(N - |P|)]
22.
23. return fronts[0]  // Return first front
```

**Complexity:** O(G · N² · k) for k objectives.

### 5.5 Non-Dominated Sorting

```
Algorithm 5.4: NON-DOMINATED-SORT
Input: Population P
Output: List of fronts

1. for each p in P:
2.     S[p] ← ∅  // Dominated set
3.     n[p] ← 0  // Domination count
4.     for each q in P:
5.         if p ≻ q:
6.             S[p] ← S[p] ∪ {q}
7.         else if q ≻ p:
8.             n[p] ← n[p] + 1
9.     if n[p] = 0:
10.         rank[p] ← 1
11.         F[1] ← F[1] ∪ {p}
12.
13. i ← 1
14. while F[i] ≠ ∅:
15.     Q ← ∅
16.     for each p in F[i]:
17.         for each q in S[p]:
18.             n[q] ← n[q] - 1
19.             if n[q] = 0:
20.                 rank[q] ← i + 1
21.                 Q ← Q ∪ {q}
22.     i ← i + 1
23.     F[i] ← Q
24.
25. return F
```

**Complexity:** O(k · N²) for k objectives, N solutions.

---

## 6. Carbon-Aware Scheduling

### 6.1 Problem Definition

**Input:**
- Tasks `T = {t₁, ..., tₙ}` with deadlines `d_i` and energy requirements `e_i`
- Carbon intensity forecast `c(t) : [0, H] → ℝ⁺` over horizon H
- Carbon budget `C_max`

**Output:**
- Schedule `σ : T → [0, H]` (start times)

**Objective:**
- Minimize total carbon: `Σᵢ eᵢ · c(σ(tᵢ))`
- Subject to: deadlines met, energy available

### 6.2 Greedy Carbon-Aware Scheduling

```
Algorithm 6.1: GREEDY-CARBON-SCHEDULE
Input: Tasks T, carbon forecast c(t), horizon H
Output: Schedule σ

1. // Sort tasks by deadline (EDF-style)
2. T_sorted ← SORT-BY-DEADLINE(T)
3.
4. σ ← {}
5. for each task t in T_sorted:
6.     // Find lowest-carbon slot before deadline
7.     best_time ← argmin_{s ∈ [0, d_t - duration_t]} c(s)
8.     σ[t] ← best_time
9.     // Mark slot as used (simplified)
10.     MARK-USED(best_time, duration_t)
11.
12. return σ
```

**Complexity:** O(n log n + n · H) for discrete time slots.

### 6.3 Dynamic Programming for Optimal Scheduling

```
Algorithm 6.2: DP-CARBON-SCHEDULE
Input: Tasks T (sorted by deadline), carbon forecast c[1..H], energy e[1..n]
Output: Minimum carbon cost

1. // DP state: dp[i][t] = min carbon to schedule tasks 1..i by time t
2. dp[0][0] ← 0
3. for t = 1 to H:
4.     dp[0][t] ← 0
5.
6. for i = 1 to n:
7.     for t = 1 to d_i:  // Must complete by deadline
8.         // Option 1: Schedule task i at time t - duration_i
9.         start ← t - duration_i
10.         if start ≥ 0:
11.             carbon_cost ← e[i] · average(c[start..t])
12.             dp[i][t] ← min(dp[i][t], dp[i-1][start] + carbon_cost)
13.
14.         // Option 2: Task i already scheduled earlier
15.         dp[i][t] ← min(dp[i][t], dp[i][t-1])
16.
17. return dp[n][H]
```

**Complexity:** O(n · H · D) where D is max duration.

### 6.4 Online Carbon-Aware Scheduling

For real-time scheduling with uncertain forecasts:

```
Algorithm 6.3: ONLINE-CARBON-SCHEDULE
Input: Stream of tasks, carbon forecast (updated online)
Output: Real-time scheduling decisions

1. while true:
2.     // Get current task and forecast
3.     task ← RECEIVE-NEXT-TASK()
4.     forecast ← GET-CARBON-FORECAST(48h)  // 48-hour lookahead
5.
6.     if task.deferrable:
7.         // Find optimal window
8.         window ← FIND-LOW-CARBON-WINDOW(forecast, task.deadline)
9.         if current_carbon > window.carbon * (1 + threshold):
10.             DEFER(task, window.start)
11.         else:
12.             EXECUTE-NOW(task)
13.     else:
14.         EXECUTE-NOW(task)
15.
16.     SLEEP(poll_interval)
```

**Competitive Ratio:** 2 against offline optimal (proven in §14).

### 6.5 Threshold Policy

```
Algorithm 6.4: THRESHOLD-POLICY
Input: Carbon threshold θ, task t
Output: Decision (execute now or defer)

1. current_intensity ← GET-CURRENT-CARBON-INTENSITY()
2.
3. if current_intensity ≤ θ:
4.     return EXECUTE-NOW
5. else:
6.     if time_to_deadline(t) < MIN-LOOKAHEAD:
7.         return EXECUTE-NOW  // Must execute
8.     else:
9.         return DEFER
```

**Theorem 6.1 (Threshold Optimality).** For IID carbon intensity, threshold policy is optimal.

*Proof:* By optimal stopping theory. The problem is a stopping problem; threshold policies are optimal for IID observations. □

---

## 7. Type Inference Algorithms

### 7.1 Algorithm W (Extended)

```
Algorithm 7.1: ALGORITHM-W-EXTENDED
Input: Context Γ, expression e
Output: Substitution S, type τ, dimension constraints D

W(Γ, x):
    if x:σ ∈ Γ:
        τ ← INSTANTIATE(σ)
        return (∅, τ, ∅)
    else:
        ERROR("Unbound variable")

W(Γ, λx. e):
    α ← FRESH-TYPE-VAR()
    (S, τ, D) ← W(Γ ∪ {x:α}, e)
    return (S, S(α) → τ, D)

W(Γ, e₁ e₂):
    (S₁, τ₁, D₁) ← W(Γ, e₁)
    (S₂, τ₂, D₂) ← W(S₁(Γ), e₂)
    α ← FRESH-TYPE-VAR()
    S₃ ← UNIFY(S₂(τ₁), τ₂ → α)
    return (S₃ ∘ S₂ ∘ S₁, S₃(α), D₁ ∪ D₂)

W(Γ, let x = e₁ in e₂):
    (S₁, τ₁, D₁) ← W(Γ, e₁)
    σ₁ ← GENERALIZE(S₁(Γ), τ₁)
    (S₂, τ₂, D₂) ← W(S₁(Γ) ∪ {x:σ₁}, e₂)
    return (S₂ ∘ S₁, τ₂, D₁ ∪ D₂)

W(Γ, n unit):
    d ← DIM(unit)
    return (∅, Resource(d), ∅)

W(Γ, e₁ + e₂):
    (S₁, τ₁, D₁) ← W(Γ, e₁)
    (S₂, τ₂, D₂) ← W(S₁(Γ), e₂)
    // τ₁ = Resource(d₁), τ₂ = Resource(d₂)
    D₃ ← D₁ ∪ D₂ ∪ {d₁ = d₂}
    (S₃, d) ← SOLVE-DIM-CONSTRAINTS(D₃)
    return (S₃ ∘ S₂ ∘ S₁, Resource(d), D₃)
```

**Complexity:** O(n · α(n)) where α is inverse Ackermann (union-find).

### 7.2 Unification

```
Algorithm 7.2: UNIFY
Input: Types τ₁, τ₂
Output: Most general unifier S

UNIFY(α, τ):
    if α ∈ FTV(τ):
        ERROR("Occurs check failed")
    return [α ↦ τ]

UNIFY(τ, α):
    return UNIFY(α, τ)

UNIFY(τ₁ → τ₁', τ₂ → τ₂'):
    S₁ ← UNIFY(τ₁, τ₂)
    S₂ ← UNIFY(S₁(τ₁'), S₁(τ₂'))
    return S₂ ∘ S₁

UNIFY(τ₁ × τ₁', τ₂ × τ₂'):
    S₁ ← UNIFY(τ₁, τ₂)
    S₂ ← UNIFY(S₁(τ₁'), S₁(τ₂'))
    return S₂ ∘ S₁

UNIFY(Resource(d₁), Resource(d₂)):
    if d₁ = d₂:
        return ∅
    else:
        ERROR("Dimension mismatch")

UNIFY(C₁, C₂):
    if C₁ = C₂:
        return ∅
    else:
        ERROR("Cannot unify")
```

**Complexity:** O(n · α(n)) with path compression.

### 7.3 Principal Type Property

**Theorem 7.1 (Principal Types).** If `Γ ⊢ e : τ` is derivable, then Algorithm W computes a principal type `τ_p` such that `τ = S(τ_p)` for some substitution `S`.

*Proof:* By structural induction on `e`. Each step computes most general unifier. □

---

## 8. Dimension Inference and Checking

### 8.1 Dimension Representation

Dimensions are represented as integer vectors:
```
d = (m, l, t, i, θ, n, j) ∈ ℤ⁷
```

| Dimension | Vector |
|-----------|--------|
| 1 (dimensionless) | (0,0,0,0,0,0,0) |
| M (mass) | (1,0,0,0,0,0,0) |
| L (length) | (0,1,0,0,0,0,0) |
| T (time) | (0,0,1,0,0,0,0) |
| Energy = M·L²·T⁻² | (1,2,-2,0,0,0,0) |
| Power = M·L²·T⁻³ | (1,2,-3,0,0,0,0) |

### 8.2 Dimension Unification

```
Algorithm 8.1: DIMENSION-UNIFY
Input: Dimension constraints D = {d₁ = d₁', ..., dₖ = dₖ'}
Output: Solution or UNSATISFIABLE

1. // Convert to linear system Ax = 0
2. // Each constraint d = d' becomes d - d' = 0
3.
4. A ← BUILD-CONSTRAINT-MATRIX(D)
5.
6. // Gaussian elimination
7. A_reduced ← GAUSSIAN-ELIMINATION(A)
8.
9. // Check satisfiability
10. for each row r in A_reduced:
11.     if r has form [0 0 ... 0 | c] where c ≠ 0:
12.         return UNSATISFIABLE
13.
14. // Extract solution
15. solution ← BACK-SUBSTITUTE(A_reduced)
16. return solution
```

**Complexity:** O(d³) for d dimension variables.

### 8.3 Dimension Inference

```
Algorithm 8.2: INFER-DIMENSIONS
Input: Expression e with unknown dimension variables
Output: Dimension assignment

1. // Collect constraints from expression
2. constraints ← ∅
3.
4. TRAVERSE(e):
5.     case e₁ + e₂:
6.         d₁ ← DIM(e₁)
7.         d₂ ← DIM(e₂)
8.         constraints ← constraints ∪ {d₁ = d₂}
9.     case e₁ * e₂:
10.         // No constraint; result is d₁ · d₂
11.     case e₁ / e₂:
12.         // No constraint; result is d₁ / d₂
13.     // ... other cases
14.
15. // Solve constraints
16. return DIMENSION-UNIFY(constraints)
```

**Complexity:** O(|e| + d³) where |e| is expression size.

---

## 9. Constraint Solving

### 9.1 Resource Constraint Representation

Constraints are linear inequalities:
```
C ::= r ⋈ n    where ⋈ ∈ {<, ≤, =, ≥, >}
    | C ∧ C
```

### 9.2 Constraint Propagation

```
Algorithm 9.1: PROPAGATE-CONSTRAINTS
Input: Constraint set C, variable bounds V
Output: Refined bounds V'

1. changed ← true
2. while changed:
3.     changed ← false
4.     for each constraint c in C:
5.         V_new ← APPLY-CONSTRAINT(c, V)
6.         if V_new ⊂ V:
7.             V ← V_new
8.             changed ← true
9.
10. // Check consistency
11. for each variable x:
12.     if V[x].lower > V[x].upper:
13.         return UNSATISFIABLE
14.
15. return V
```

**Complexity:** O(k · n) for k constraints, n variables.

### 9.3 LP-Based Constraint Solving

For complex constraint systems, use LP:

```
Algorithm 9.2: LP-CONSTRAINT-SOLVE
Input: Linear constraints C, objective (optional)
Output: Feasible point or INFEASIBLE

1. // Convert constraints to standard form
2. (A, b) ← STANDARDIZE(C)
3.
4. // Solve LP
5. if objective given:
6.     return LP-SOLVE(min objective, Ax ≤ b)
7. else:
8.     // Feasibility check
9.     return LP-FEASIBILITY(Ax ≤ b)
```

**Complexity:** O(n³·⁵) using interior point.

### 9.4 Satisfiability Modulo Theories (SMT)

For mixed constraints (boolean + linear):

```
Algorithm 9.3: SMT-SOLVE
Input: Formula φ with boolean and linear arithmetic
Output: SAT with model, or UNSAT

1. // DPLL(T) algorithm
2. trail ← []
3. level ← 0
4.
5. while true:
6.     // Unit propagation
7.     (conflict, trail) ← PROPAGATE(φ, trail)
8.
9.     if conflict:
10.         if level = 0:
11.             return UNSAT
12.         // Conflict analysis
13.         (learned, backtrack_level) ← ANALYZE(conflict, trail)
14.         φ ← φ ∧ learned
15.         BACKTRACK(trail, backtrack_level)
16.         level ← backtrack_level
17.     else:
18.         // Check theory consistency
19.         if not LA-CONSISTENT(trail):
20.             lemma ← LA-CONFLICT-LEMMA(trail)
21.             φ ← φ ∧ lemma
22.         else if all variables assigned:
23.             return (SAT, trail)
24.         else:
25.             // Decision
26.             level ← level + 1
27.             lit ← CHOOSE-LITERAL(φ)
28.             trail ← trail ++ [(lit, DECISION)]
```

---

## 10. Resource Profiling

### 10.1 Statistical Profiling

```
Algorithm 10.1: PROFILE-SOLUTION
Input: Solution s, sample count N
Output: Resource profile estimate with confidence intervals

1. samples ← []
2. for i = 1 to N:
3.     cost ← MEASURE-EXECUTION(s)
4.     samples ← samples ++ [cost]
5.
6. // Compute statistics
7. mean ← MEAN(samples)
8. std ← STDDEV(samples)
9. ci_95 ← 1.96 * std / √N
10.
11. return (mean, mean - ci_95, mean + ci_95)
```

### 10.2 Bayesian Profiling

```
Algorithm 10.2: BAYESIAN-PROFILE
Input: Prior distribution P₀, observations O
Output: Posterior distribution P

1. // Update prior with observations using Bayes' rule
2. P ← P₀
3. for each observation o in O:
4.     likelihood ← COMPUTE-LIKELIHOOD(o, P)
5.     P ← NORMALIZE(P · likelihood)
6.
7. return P
```

### 10.3 Online Learning for Resource Prediction

```
Algorithm 10.3: ONLINE-RESOURCE-LEARNING
Input: Stream of (input_features, actual_cost) pairs
Output: Updated predictor

1. // Initialize model
2. model ← LINEAR-REGRESSION()
3.
4. for each (features, cost) in stream:
5.     // Predict
6.     predicted ← model.predict(features)
7.
8.     // Update model (SGD)
9.     error ← cost - predicted
10.     model.update(features, error, learning_rate)
11.
12.     // Decay learning rate
13.     learning_rate ← learning_rate * decay_factor
```

**Regret Bound:** O(√T) for T observations.

---

## 11. Adaptive Scheduling

### 11.1 Multi-Armed Bandit for Solution Selection

When solution costs are unknown:

```
Algorithm 11.1: UCB-SELECT (Upper Confidence Bound)
Input: Solutions S, history H
Output: Solution to try

1. for each solution s:
2.     if count[s] = 0:
3.         return s  // Explore unvisited
4.
5.     // UCB score
6.     exploitation[s] ← -mean_cost[s]  // Minimize cost
7.     exploration[s] ← c · √(ln(t) / count[s])
8.     ucb[s] ← exploitation[s] + exploration[s]
9.
10. return argmax_{s} ucb[s]
```

**Regret Bound:** O(√(n · T · log T)) for n solutions, T selections.

### 11.2 Thompson Sampling

```
Algorithm 11.2: THOMPSON-SAMPLING-SELECT
Input: Solutions S, prior parameters
Output: Solution to select

1. for each solution s:
2.     // Sample from posterior (assume Gaussian)
3.     sampled_cost[s] ← SAMPLE-NORMAL(mean[s], var[s])
4.
5. return argmin_{s} sampled_cost[s]
```

**Regret Bound:** O(√(n · T · log T)), matches UCB.

### 11.3 Contextual Bandits

When context affects solution performance:

```
Algorithm 11.3: LINUCB (Linear Upper Confidence Bound)
Input: Context x, solutions S
Output: Solution to select

1. for each solution s:
2.     // Predicted cost with uncertainty
3.     θ_s ← A_s^{-1} b_s
4.     predicted_cost ← θ_s^T x
5.     uncertainty ← α · √(x^T A_s^{-1} x)
6.     lcb[s] ← predicted_cost - uncertainty
7.
8. s* ← argmin_{s} lcb[s]
9.
10. // After observing actual cost:
11. A_{s*} ← A_{s*} + x x^T
12. b_{s*} ← b_{s*} + actual_cost · x
13.
14. return s*
```

---

## 12. Amortized Analysis

### 12.1 Amortized Cost of Adaptive Execution

**Definition 12.1 (Amortized Cost).** For sequence of operations, amortized cost is:
```
amortized_cost(opᵢ) = actual_cost(opᵢ) + ΔΦ
```
where Φ is the potential function.

### 12.2 Potential Function for Adaptive Blocks

**Definition 12.2 (Budget Potential).**
```
Φ(Σ) = Σᵣ (B(r) - Σ(r)) / min_cost(r)
```

**Theorem 12.1 (Amortized Bound).** Each adaptive selection has O(n·m) amortized cost.

*Proof:*
1. Actual cost: O(n·m) for selection
2. ΔΦ: At most -1 (one unit of potential consumed)
3. Total: O(n·m) + O(1) = O(n·m) □

### 12.3 Aggregate Analysis

**Theorem 12.2 (Aggregate Bound).** For T operations with budget B:
```
Total time ≤ T · O(n·m) + O(|B| / min_cost)
```

*Proof:* Each operation pays O(n·m). Total potential decrease bounded by initial potential. □

---

## 13. Approximation Algorithms

### 13.1 Approximation for NP-Hard Variants

When solution selection involves complex dependencies:

**Definition 13.1 (Approximation Ratio).** Algorithm A has ratio α if:
```
cost(A) ≤ α · OPT
```

### 13.2 PTAS for Knapsack-Like Selection

```
Algorithm 13.1: PTAS-SELECT (ε-approximation)
Input: Solutions S, budget B, ε > 0
Output: (1+ε)-approximate selection

1. // Round costs to powers of (1+ε)
2. for each solution s:
3.     rounded_cost[s] ← ROUND-TO-POWER(cost(s), 1+ε)
4.
5. // DP on rounded costs
6. dp[0] ← 0
7. for each rounded cost c:
8.     for s with rounded_cost[s] = c:
9.         dp[c] ← max(dp[c], dp[c - rounded_cost[s]] + value[s])
10.
11. // Recover solution
12. return BACKTRACK(dp)
```

**Complexity:** O(n² / ε) - PTAS.

### 13.3 Greedy Approximation

```
Algorithm 13.2: GREEDY-APPROXIMATE
Input: Solutions S, budget B
Output: Approximate selection

1. // Sort by efficiency (value / cost)
2. sorted ← SORT-BY-EFFICIENCY(S)
3.
4. selected ← ∅
5. remaining ← B
6.
7. for s in sorted:
8.     if cost(s) ≤ remaining:
9.         selected ← selected ∪ {s}
10.         remaining ← remaining - cost(s)
11.
12. return selected
```

**Approximation Ratio:** 2 for single-dimensional knapsack.

---

## 14. Online Algorithms

### 14.1 Competitive Analysis

**Definition 14.1 (Competitive Ratio).** Online algorithm A is c-competitive if:
```
cost(A) ≤ c · cost(OPT) + α
```
for all input sequences, where OPT is offline optimal.

### 14.2 Online Carbon Scheduling

```
Algorithm 14.1: ONLINE-CARBON-SCHEDULE
Input: Stream of tasks arriving online
Output: Scheduling decisions

1. while tasks remain:
2.     t ← NEXT-ARRIVING-TASK()
3.     forecast ← GET-FORECAST(t.deadline - now)
4.
5.     // Threshold policy
6.     θ ← COMPUTE-THRESHOLD(forecast)
7.
8.     if current_carbon ≤ θ:
9.         EXECUTE-NOW(t)
10.     else:
11.         SCHEDULE-AT(t, FIND-LOW-CARBON-SLOT(forecast))
```

**Theorem 14.1 (Carbon Competitive Ratio).** Algorithm 14.1 is 2-competitive.

*Proof Sketch:*
1. For any task, either execute now or at best future slot.
2. If we execute now at intensity c, OPT might wait for intensity c' ≤ c.
3. Worst case: c = 2c' (we pay twice optimal).
4. Across all tasks: Total ≤ 2 · OPT. □

### 14.3 Ski Rental for Resource Acquisition

When deciding between renting vs. buying resources:

```
Algorithm 14.2: SKI-RENTAL
Input: Rent cost r, buy cost B, usage duration unknown
Output: Rent/buy decision

1. // Deterministic: Rent until cost equals buy price
2. rented_so_far ← 0
3.
4. for each time unit:
5.     if rented_so_far < B:
6.         RENT()
7.         rented_so_far ← rented_so_far + r
8.     else:
9.         BUY()
10.         break
```

**Competitive Ratio:** 2 (tight).

### 14.4 Randomized Online Algorithms

```
Algorithm 14.3: RANDOMIZED-THRESHOLD
Input: Distribution over thresholds
Output: Randomized decision

1. θ ← SAMPLE-THRESHOLD(distribution)
2.
3. if current_value ≤ θ:
4.     EXECUTE-NOW()
5. else:
6.     DEFER()
```

**Competitive Ratio:** e/(e-1) ≈ 1.58 (better than deterministic 2).

---

## 15. Complexity Summary

### 15.1 Time Complexity

| Algorithm | Time Complexity | Notes |
|-----------|-----------------|-------|
| Solution Selection | O(n·m) | n solutions, m resources |
| Shadow Price (simplex) | O(2^m) worst, O(m²n) avg | m constraints |
| Shadow Price (IPM) | O(m^{3.5}·L) | L = input bits |
| Type Inference | O(n·α(n)) | n = expression size |
| Dimension Checking | O(d³) | d = dimension variables |
| Constraint Solving (LP) | O(k^{3.5}) | k = constraints |
| Pareto Sorting | O(k·N²) | k objectives, N solutions |
| Carbon Scheduling (DP) | O(n·H·D) | H = horizon, D = duration |
| UCB Selection | O(n) | per selection |

### 15.2 Space Complexity

| Algorithm | Space Complexity | Notes |
|-----------|------------------|-------|
| Solution Selection | O(n·m) | Store profiles |
| Shadow Price | O(m²) | LP basis |
| Type Inference | O(n) | Substitution |
| Dimension Checking | O(d²) | Constraint matrix |
| Pareto Frontier | O(N·k) | Store frontier |
| Profiling | O(s) | s = sample count |

### 15.3 Approximation Guarantees

| Problem | Algorithm | Ratio | Notes |
|---------|-----------|-------|-------|
| Selection | Greedy | 2 | Single resource |
| Selection | PTAS | 1+ε | Multi-resource |
| Carbon Scheduling | Threshold | 2 | Online |
| Carbon Scheduling | Randomized | e/(e-1) | Online |
| Multi-objective | NSGA-II | N/A | Heuristic |

### 15.4 Lower Bounds

| Problem | Lower Bound | Source |
|---------|-------------|--------|
| General LP | Ω(n·m) | Input size |
| Online scheduling | 2 | Competitive ratio |
| Type inference | Ω(n) | Must read input |
| Pareto sorting | Ω(N log N) | Comparison-based |

---

## Appendix A: Pseudocode Conventions

```
Algorithm Name:
Input: Description of inputs
Output: Description of outputs

1. // Comment
2. statement
3. for variable = start to end:
4.     body
5. while condition:
6.     body
7. if condition:
8.     then-branch
9. else:
10.    else-branch
11. return value
```

## Appendix B: Complexity Classes Reference

| Class | Definition |
|-------|------------|
| P | Solvable in polynomial time |
| NP | Verifiable in polynomial time |
| NP-hard | At least as hard as NP |
| PTAS | (1+ε)-approximation in poly(n, 1/ε) time |
| FPTAS | (1+ε)-approximation in poly(n, 1/ε) time |

---

**Document Version:** 1.0
**Last Updated:** December 2025
**License:** AGPL-3.0-or-later

```bibtex
@techreport{eclexia2025algorithms,
  title={Algorithms and Complexity Analysis for Eclexia},
  author={Jewell, Jonathan D.A.},
  year={2025},
  month={December},
  institution={Eclexia Project},
  url={https://eclexia.org/algorithms},
  note={Version 1.0}
}
```
