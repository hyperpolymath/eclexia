# Formal Proofs for Eclexia

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

**Version:** 1.0
**Date:** December 2025
**Authors:** Jonathan D.A. Jewell
**Status:** Research Preview

---

## Abstract

This document presents the formal mathematical foundations and correctness proofs for Eclexia, a programming language implementing the Economics-as-Code paradigm. We establish: (1) type safety via progress and preservation theorems; (2) dimensional correctness ensuring no unit mismatches at runtime; (3) resource safety guaranteeing no budget violations; (4) economic optimality proving shadow prices converge to optimal values; and (5) termination under resource bounds. Proofs are presented in a rigorous mathematical style suitable for formalization in proof assistants.

---

## Table of Contents

1. [Preliminaries](#1-preliminaries)
2. [Type Safety](#2-type-safety)
3. [Dimensional Correctness](#3-dimensional-correctness)
4. [Type Inference](#4-type-inference)
5. [Operational Semantics Properties](#5-operational-semantics-properties)
6. [Resource Safety](#6-resource-safety)
7. [Determinism](#7-determinism)
8. [Economic Optimality](#8-economic-optimality)
9. [Termination](#9-termination)
10. [Soundness of Constraint Solving](#10-soundness-of-constraint-solving)
11. [Metatheoretic Properties](#11-metatheoretic-properties)

---

## 1. Preliminaries

### 1.1 Notational Conventions

We use the following notation throughout:

| Symbol | Meaning |
|--------|---------|
| `Γ` | Type environment (context) |
| `Σ` | Resource state |
| `B` | Budget (resource bounds) |
| `τ, σ` | Types |
| `ρ` | Resource types |
| `d` | Dimensions |
| `λ` | Shadow prices |
| `e, e'` | Expressions |
| `v` | Values |
| `⊢` | Typing judgment |
| `⟶` | Single-step reduction |
| `⟶*` | Multi-step reduction (reflexive transitive closure) |
| `[x := e]` | Substitution of `e` for `x` |
| `FV(e)` | Free variables in `e` |
| `dom(Γ)` | Domain of environment `Γ` |

### 1.2 Language Syntax

**Expressions:**
```
e ::= x                                    (variable)
    | n | r | b | s                        (literals: int, real, bool, string)
    | λx:τ. e                              (abstraction)
    | e₁ e₂                                (application)
    | let x = e₁ in e₂                     (let binding)
    | if e₁ then e₂ else e₃                (conditional)
    | (e₁, e₂)                             (pair)
    | fst e | snd e                        (projections)
    | inl e | inr e                        (injections)
    | match e with inl x => e₁ | inr y => e₂  (case)
    | n unit                               (resource literal)
    | e₁ ⊕ e₂                              (resource operations: +, *, /)
    | adaptive { sᵢ }                      (adaptive block)
```

**Solutions (within adaptive blocks):**
```
s ::= @solution name: @when g @provides p { e }
g ::= boolean expression (guard)
p ::= resource profile { r₁: v₁, ..., rₙ: vₙ }
```

**Types:**
```
τ ::= Unit | Bool | Int | Float | String   (base types)
    | τ₁ → τ₂                              (function)
    | τ₁ × τ₂                              (product)
    | τ₁ + τ₂                              (sum)
    | ∀α. τ                                (universal)
    | α                                    (type variable)
    | ρ[d]                                 (resource type with dimension)
    | τ @requires C                        (constrained type)
```

**Dimensions:**
```
d ::= 1                                    (dimensionless)
    | M | L | T | I | Θ | N | J            (base dimensions)
    | d₁ · d₂                              (product)
    | d₁ / d₂                              (quotient)
    | d^n                                  (exponentiation)
```

### 1.3 Type Environments

**Definition 1.1 (Type Environment).** A type environment `Γ` is a finite map from variables to types:
```
Γ ::= ∅ | Γ, x:τ
```

**Definition 1.2 (Environment Extension).** `Γ, x:τ` extends `Γ` with binding `x:τ`, where `x ∉ dom(Γ)`.

**Definition 1.3 (Environment Lookup).** `Γ(x) = τ` iff `x:τ ∈ Γ`.

### 1.4 Resource States

**Definition 1.4 (Resource State).** A resource state `Σ: R → ℝ≥0` maps each resource type to current consumption.

**Definition 1.5 (Budget).** A budget `B: R → ℝ≥0 ∪ {∞}` maps each resource type to maximum allowed consumption.

**Definition 1.6 (Budget Compliance).** State `Σ` complies with budget `B`, written `Σ ⊑ B`, iff `∀r ∈ R. Σ(r) ≤ B(r)`.

---

## 2. Type Safety

We prove type safety via the standard progress and preservation theorems.

### 2.1 Typing Rules

**Typing Judgment:** `Γ ⊢ e : τ` means "in environment `Γ`, expression `e` has type `τ`."

#### 2.1.1 Structural Rules

```

─────────────────  (T-Unit)
Γ ⊢ () : Unit


─────────────────  (T-Int)
Γ ⊢ n : Int


─────────────────  (T-Float)
Γ ⊢ r : Float


─────────────────  (T-Bool)
Γ ⊢ b : Bool


─────────────────  (T-String)
Γ ⊢ s : String


x : τ ∈ Γ
─────────────────  (T-Var)
Γ ⊢ x : τ


Γ, x:τ₁ ⊢ e : τ₂
─────────────────────────  (T-Abs)
Γ ⊢ λx:τ₁. e : τ₁ → τ₂


Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
─────────────────────────────────  (T-App)
Γ ⊢ e₁ e₂ : τ₂


Γ ⊢ e₁ : τ₁    Γ, x:τ₁ ⊢ e₂ : τ₂
─────────────────────────────────  (T-Let)
Γ ⊢ let x = e₁ in e₂ : τ₂


Γ ⊢ e₁ : Bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ
───────────────────────────────────────────  (T-If)
Γ ⊢ if e₁ then e₂ else e₃ : τ


Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂
───────────────────────────  (T-Pair)
Γ ⊢ (e₁, e₂) : τ₁ × τ₂


Γ ⊢ e : τ₁ × τ₂
─────────────────  (T-Fst)
Γ ⊢ fst e : τ₁


Γ ⊢ e : τ₁ × τ₂
─────────────────  (T-Snd)
Γ ⊢ snd e : τ₂


Γ ⊢ e : τ₁
─────────────────────  (T-Inl)
Γ ⊢ inl e : τ₁ + τ₂


Γ ⊢ e : τ₂
─────────────────────  (T-Inr)
Γ ⊢ inr e : τ₁ + τ₂


Γ ⊢ e : τ₁ + τ₂    Γ, x:τ₁ ⊢ e₁ : τ    Γ, y:τ₂ ⊢ e₂ : τ
─────────────────────────────────────────────────────────  (T-Match)
Γ ⊢ match e with inl x => e₁ | inr y => e₂ : τ


Γ ⊢ e : τ    α ∉ FTV(Γ)
───────────────────────  (T-TAbs)
Γ ⊢ e : ∀α. τ


Γ ⊢ e : ∀α. τ
─────────────────────  (T-TApp)
Γ ⊢ e : τ[α := σ]
```

#### 2.1.2 Resource Rules

```
dim(unit) = d
─────────────────────  (T-Resource)
Γ ⊢ n unit : ρ[d]


Γ ⊢ e₁ : ρ[d]    Γ ⊢ e₂ : ρ[d]
───────────────────────────────  (T-RAdd)
Γ ⊢ e₁ + e₂ : ρ[d]


Γ ⊢ e₁ : ρ[d₁]    Γ ⊢ e₂ : ρ[d₂]
─────────────────────────────────  (T-RMul)
Γ ⊢ e₁ * e₂ : ρ[d₁ · d₂]


Γ ⊢ e₁ : ρ[d₁]    Γ ⊢ e₂ : ρ[d₂]    d₂ ≠ 0
───────────────────────────────────────────  (T-RDiv)
Γ ⊢ e₁ / e₂ : ρ[d₁ / d₂]
```

#### 2.1.3 Constraint Rules

```
Γ ⊢ e : τ    Γ ⊢ C : Constraint
─────────────────────────────────  (T-Constrain)
Γ ⊢ e @requires C : τ @requires C


Γ ⊢ e₁ : τ₁ @requires C → τ₂    Γ ⊢ e₂ : τ₁    C ⊆ current_budget
──────────────────────────────────────────────────────────────────  (T-CApp)
Γ ⊢ e₁ e₂ : τ₂
```

#### 2.1.4 Adaptive Block Rules

```
∀i ∈ 1..n. Γ ⊢ gᵢ : Bool
∀i ∈ 1..n. Γ ⊢ pᵢ : ResourceProfile
∀i ∈ 1..n. Γ ⊢ eᵢ : τ
∀i ∈ 1..n. satisfies(pᵢ, requires)
──────────────────────────────────────────────────────────  (T-Adaptive)
Γ ⊢ adaptive { @solution sᵢ: @when gᵢ @provides pᵢ { eᵢ } }ᵢ : τ
```

### 2.2 Values

**Definition 2.1 (Values).** The set of values is defined inductively:
```
v ::= () | n | r | b | s                   (literals)
    | λx:τ. e                              (abstractions)
    | (v₁, v₂)                             (pairs of values)
    | inl v | inr v                        (tagged values)
    | n unit                               (resource values)
```

### 2.3 Canonical Forms

**Lemma 2.1 (Canonical Forms).**

1. If `∅ ⊢ v : Unit` and `v` is a value, then `v = ()`.
2. If `∅ ⊢ v : Int` and `v` is a value, then `v = n` for some integer `n`.
3. If `∅ ⊢ v : Float` and `v` is a value, then `v = r` for some real `r`.
4. If `∅ ⊢ v : Bool` and `v` is a value, then `v = true` or `v = false`.
5. If `∅ ⊢ v : String` and `v` is a value, then `v = s` for some string `s`.
6. If `∅ ⊢ v : τ₁ → τ₂` and `v` is a value, then `v = λx:τ₁. e` for some `x, e`.
7. If `∅ ⊢ v : τ₁ × τ₂` and `v` is a value, then `v = (v₁, v₂)` for some `v₁, v₂`.
8. If `∅ ⊢ v : τ₁ + τ₂` and `v` is a value, then `v = inl v'` or `v = inr v'` for some `v'`.
9. If `∅ ⊢ v : ρ[d]` and `v` is a value, then `v = n unit` where `dim(unit) = d`.

*Proof:* By inspection of the typing rules. Each type has a unique syntactic form for its values. □

### 2.4 Substitution Lemma

**Lemma 2.2 (Substitution).** If `Γ, x:τ' ⊢ e : τ` and `Γ ⊢ e' : τ'`, then `Γ ⊢ e[x := e'] : τ`.

*Proof:* By induction on the derivation of `Γ, x:τ' ⊢ e : τ`.

**Case T-Var:** `e = y` for some variable `y`.
- Subcase `y = x`: Then `τ = τ'` and `e[x := e'] = e'`. By assumption, `Γ ⊢ e' : τ'`. ✓
- Subcase `y ≠ x`: Then `y:τ ∈ Γ` and `e[x := e'] = y`. By T-Var, `Γ ⊢ y : τ`. ✓

**Case T-Abs:** `e = λy:σ. e₁` and `τ = σ → τ₁` where `Γ, x:τ', y:σ ⊢ e₁ : τ₁`.
- Assume `y ∉ FV(e')` and `y ≠ x` (by α-renaming if necessary).
- By IH: `Γ, y:σ ⊢ e₁[x := e'] : τ₁`.
- By T-Abs: `Γ ⊢ λy:σ. e₁[x := e'] : σ → τ₁`. ✓

**Case T-App:** `e = e₁ e₂` where `Γ, x:τ' ⊢ e₁ : σ → τ` and `Γ, x:τ' ⊢ e₂ : σ`.
- By IH: `Γ ⊢ e₁[x := e'] : σ → τ` and `Γ ⊢ e₂[x := e'] : σ`.
- By T-App: `Γ ⊢ (e₁[x := e']) (e₂[x := e']) : τ`. ✓

*Remaining cases follow similarly.* □

### 2.5 Progress Theorem

**Theorem 2.1 (Progress).** If `∅ ⊢ e : τ`, then either:
1. `e` is a value, or
2. There exists `e'` such that `e ⟶ e'`.

*Proof:* By induction on the derivation of `∅ ⊢ e : τ`.

**Case T-Var:** Impossible—no variable can be typed in an empty environment.

**Case T-Unit, T-Int, T-Float, T-Bool, T-String:** `e` is already a value. ✓

**Case T-Abs:** `e = λx:τ₁. e'` is a value. ✓

**Case T-App:** `e = e₁ e₂` where `∅ ⊢ e₁ : τ' → τ` and `∅ ⊢ e₂ : τ'`.
- By IH on `e₁`: either `e₁` is a value or `e₁ ⟶ e₁'`.
  - If `e₁ ⟶ e₁'`: By E-App1, `e₁ e₂ ⟶ e₁' e₂`. ✓
  - If `e₁` is a value: By IH on `e₂`: either `e₂` is a value or `e₂ ⟶ e₂'`.
    - If `e₂ ⟶ e₂'`: By E-App2, `v₁ e₂ ⟶ v₁ e₂'`. ✓
    - If `e₂` is a value: By Canonical Forms (6), `e₁ = λx:τ'. e'₁`. By E-Beta, `(λx:τ'. e'₁) v₂ ⟶ e'₁[x := v₂]`. ✓

**Case T-Let:** `e = let x = e₁ in e₂`.
- By IH on `e₁`: either `e₁` is a value or `e₁ ⟶ e₁'`.
  - If `e₁ ⟶ e₁'`: By E-Let1, `let x = e₁ in e₂ ⟶ let x = e₁' in e₂`. ✓
  - If `e₁` is a value: By E-Let2, `let x = v in e₂ ⟶ e₂[x := v]`. ✓

**Case T-If:** `e = if e₁ then e₂ else e₃`.
- By IH on `e₁`: either `e₁` is a value or `e₁ ⟶ e₁'`.
  - If `e₁ ⟶ e₁'`: By E-If, `if e₁ then e₂ else e₃ ⟶ if e₁' then e₂ else e₃`. ✓
  - If `e₁` is a value: By Canonical Forms (4), `e₁ = true` or `e₁ = false`.
    - If `e₁ = true`: By E-IfTrue, `if true then e₂ else e₃ ⟶ e₂`. ✓
    - If `e₁ = false`: By E-IfFalse, `if false then e₂ else e₃ ⟶ e₃`. ✓

**Case T-Pair:** `e = (e₁, e₂)`.
- By IH, each component either is a value or steps. If both values, `(v₁, v₂)` is a value. Otherwise, E-Pair1 or E-Pair2 applies. ✓

**Case T-Fst:** `e = fst e'`.
- By IH on `e'`: value or steps.
  - If steps: E-Fst applies. ✓
  - If value: By Canonical Forms (7), `e' = (v₁, v₂)`. By E-FstPair, `fst (v₁, v₂) ⟶ v₁`. ✓

**Case T-Snd:** Similar to T-Fst. ✓

**Case T-Inl, T-Inr:** Result is a value. ✓

**Case T-Match:** `e = match e' with inl x => e₁ | inr y => e₂`.
- By IH on `e'`: value or steps.
  - If steps: E-Match applies. ✓
  - If value: By Canonical Forms (8), `e' = inl v` or `e' = inr v`.
    - By E-MatchL or E-MatchR, reduction proceeds. ✓

**Case T-Resource:** `e = n unit` is a value. ✓

**Case T-RAdd:** `e = e₁ + e₂`.
- By IH, both subexpressions are values or step.
- If both values: By Canonical Forms (9), `e₁ = n₁ unit`, `e₂ = n₂ unit`. By E-RAdd, `n₁ unit + n₂ unit ⟶ (n₁ + n₂) unit`. ✓
- Otherwise: E-RAdd1 or E-RAdd2 applies. ✓

**Case T-RMul, T-RDiv:** Similar to T-RAdd. ✓

**Case T-Adaptive:** `e = adaptive { solutions }`.
- By E-Adaptive, select a feasible solution and reduce. ✓ □

### 2.6 Preservation Theorem

**Theorem 2.2 (Preservation).** If `Γ ⊢ e : τ` and `e ⟶ e'`, then `Γ ⊢ e' : τ`.

*Proof:* By induction on the derivation of `e ⟶ e'`.

**Case E-Beta:** `(λx:τ₁. e₁) v₂ ⟶ e₁[x := v₂]`.
- By inversion of T-App: `Γ ⊢ λx:τ₁. e₁ : τ₁ → τ` and `Γ ⊢ v₂ : τ₁`.
- By inversion of T-Abs: `Γ, x:τ₁ ⊢ e₁ : τ`.
- By Substitution Lemma: `Γ ⊢ e₁[x := v₂] : τ`. ✓

**Case E-App1:** `e₁ e₂ ⟶ e₁' e₂` where `e₁ ⟶ e₁'`.
- By inversion of T-App: `Γ ⊢ e₁ : τ' → τ` and `Γ ⊢ e₂ : τ'`.
- By IH: `Γ ⊢ e₁' : τ' → τ`.
- By T-App: `Γ ⊢ e₁' e₂ : τ`. ✓

**Case E-App2:** `v₁ e₂ ⟶ v₁ e₂'` where `e₂ ⟶ e₂'`.
- Similar to E-App1. ✓

**Case E-Let2:** `let x = v in e ⟶ e[x := v]`.
- By inversion of T-Let: `Γ ⊢ v : τ₁` and `Γ, x:τ₁ ⊢ e : τ`.
- By Substitution Lemma: `Γ ⊢ e[x := v] : τ`. ✓

**Case E-IfTrue:** `if true then e₁ else e₂ ⟶ e₁`.
- By inversion of T-If: `Γ ⊢ e₁ : τ`. ✓

**Case E-IfFalse:** Similar. ✓

**Case E-FstPair:** `fst (v₁, v₂) ⟶ v₁`.
- By inversion of T-Fst and T-Pair: `Γ ⊢ v₁ : τ₁`. ✓

**Case E-SndPair:** Similar. ✓

**Case E-MatchL:** `match (inl v) with inl x => e₁ | inr y => e₂ ⟶ e₁[x := v]`.
- By inversion: `Γ ⊢ inl v : τ₁ + τ₂` implies `Γ ⊢ v : τ₁`.
- Also: `Γ, x:τ₁ ⊢ e₁ : τ`.
- By Substitution Lemma: `Γ ⊢ e₁[x := v] : τ`. ✓

**Case E-MatchR:** Similar. ✓

**Case E-RAdd:** `(n₁ unit) + (n₂ unit) ⟶ (n₁ + n₂) unit`.
- By inversion: both operands have type `ρ[d]`.
- `(n₁ + n₂) unit` also has type `ρ[d]`. ✓

**Case E-RMul:** `(n₁ unit₁) * (n₂ unit₂) ⟶ (n₁ * n₂) (unit₁ · unit₂)`.
- By inversion: `Γ ⊢ n₁ unit₁ : ρ[d₁]` and `Γ ⊢ n₂ unit₂ : ρ[d₂]`.
- Result has type `ρ[d₁ · d₂]`. ✓

**Case E-RDiv:** Similar to E-RMul. ✓

**Case E-Adaptive:** `adaptive { solutions } ⟶ eᵢ`.
- By inversion of T-Adaptive: `Γ ⊢ eᵢ : τ` for all i. ✓ □

### 2.7 Type Safety Corollary

**Corollary 2.1 (Type Safety).** If `∅ ⊢ e : τ`, then either:
1. `e ⟶* v` for some value `v` with `∅ ⊢ v : τ`, or
2. `e` diverges, or
3. `e` raises a resource exhaustion error.

*Proof:* By repeated application of Progress and Preservation. Each step either produces a value (termination), enables another step (continuation), or detects no feasible solution in an adaptive block (resource exhaustion). □

---

## 3. Dimensional Correctness

We prove that well-typed programs never encounter dimension mismatches at runtime.

### 3.1 Dimension Algebra

**Definition 3.1 (Dimension).** Dimensions form a free abelian group `(D, ·, /, 1)` generated by base dimensions `{M, L, T, I, Θ, N, J}`:
- `1` is the identity (dimensionless)
- `·` is multiplication (closed, associative, commutative)
- `/` is division (d₁/d₂ = d₁ · d₂⁻¹)
- Every dimension has an inverse

**Definition 3.2 (Dimension Vector).** A dimension can be represented as a vector `d = (m, l, t, i, θ, n, j) ∈ ℤ⁷` where:
- `M^m · L^l · T^t · I^i · Θ^θ · N^n · J^j`

**Examples:**
| Physical Quantity | SI Unit | Dimension Vector |
|-------------------|---------|------------------|
| Energy | Joule (J) | (1, 2, -2, 0, 0, 0, 0) |
| Time | Second (s) | (0, 0, 1, 0, 0, 0, 0) |
| Power | Watt (W) | (1, 2, -3, 0, 0, 0, 0) |
| Force | Newton (N) | (1, 1, -2, 0, 0, 0, 0) |
| Carbon | kg CO₂e | (1, 0, 0, 0, 0, 0, 0) |

### 3.2 Dimension Compatibility

**Definition 3.3 (Dimension Compatibility).** Two resource values are *dimension-compatible* for addition iff they have the same dimension: `d₁ = d₂`.

**Definition 3.4 (Dimension Function).** `dim: Unit → D` maps unit symbols to their dimensions.

### 3.3 Dimensional Soundness

**Theorem 3.1 (Dimensional Correctness).** If `Γ ⊢ e : ρ[d]` and `e ⟶* v`, then `v = n unit` where `dim(unit) = d`.

*Proof:* By induction on the length of `e ⟶* v`.

**Base Case:** `e = v` is already a value.
- By Canonical Forms (9): `v = n unit` with `dim(unit) = d`. ✓

**Inductive Case:** `e ⟶ e' ⟶* v`.
- By Preservation: `Γ ⊢ e' : ρ[d]`.
- By IH: `v = n unit` with `dim(unit) = d`. ✓

**Key insight:** All resource operations preserve dimension consistency:
- Addition: same dimensions required by T-RAdd
- Multiplication: dimensions multiply (T-RMul)
- Division: dimensions divide (T-RDiv)

No rule allows dimension mismatch in a well-typed program. □

**Corollary 3.1 (No Dimension Mismatch).** If `∅ ⊢ e : τ`, then evaluation of `e` never attempts to add values with different dimensions.

*Proof:* T-RAdd requires both operands to have the same dimension `d`. By Preservation, this invariant holds throughout evaluation. □

### 3.4 Unit Conversion

**Definition 3.5 (Unit Conversion).** For units `u₁, u₂` with `dim(u₁) = dim(u₂)`, the conversion factor `conv(u₁, u₂) ∈ ℝ⁺` satisfies:
```
n u₁ = (n · conv(u₁, u₂)) u₂
```

**Theorem 3.2 (Conversion Correctness).** Unit conversions preserve value equality:
```
∅ ⊢ e : ρ[d] ⟹ ⟦e⟧ is independent of unit choice within dimension d
```

where `⟦·⟧` denotes semantic interpretation (physical quantity).

*Proof:* Conversion factors form a group action on numeric values, preserving the represented physical quantity. □

---

## 4. Type Inference

We prove that Eclexia's type inference algorithm is sound, complete, and terminates.

### 4.1 Algorithm W Extended

We extend Algorithm W with dimension constraint solving.

**Algorithm 4.1 (Extended Algorithm W).**

```
W(Γ, e) → (S, τ, D)
  where S is a substitution, τ is a type, D is dimension constraints

W(Γ, x) =
    if x:σ ∈ Γ then
        let τ = inst(σ) in (∅, τ, ∅)
    else error "unbound variable"

W(Γ, λx. e) =
    let α = fresh_tyvar() in
    let (S, τ, D) = W(Γ ∪ {x:α}, e) in
    (S, S(α) → τ, D)

W(Γ, e₁ e₂) =
    let (S₁, τ₁, D₁) = W(Γ, e₁) in
    let (S₂, τ₂, D₂) = W(S₁(Γ), e₂) in
    let α = fresh_tyvar() in
    let S₃ = unify(S₂(τ₁), τ₂ → α) in
    (S₃ ∘ S₂ ∘ S₁, S₃(α), D₁ ∪ D₂)

W(Γ, n unit) =
    let d = dim(unit) in
    (∅, ρ[d], ∅)

W(Γ, e₁ + e₂) =
    let (S₁, τ₁, D₁) = W(Γ, e₁) in
    let (S₂, τ₂, D₂) = W(S₁(Γ), e₂) in
    let (S₃, d) = unify_dim(τ₁, τ₂) in  // τ₁ = ρ[d₁], τ₂ = ρ[d₂], require d₁ = d₂
    (S₃ ∘ S₂ ∘ S₁, ρ[d], D₁ ∪ D₂ ∪ {d₁ = d₂})

W(Γ, e₁ * e₂) =
    let (S₁, τ₁, D₁) = W(Γ, e₁) in
    let (S₂, τ₂, D₂) = W(S₁(Γ), e₂) in
    // τ₁ = ρ[d₁], τ₂ = ρ[d₂]
    (S₂ ∘ S₁, ρ[d₁ · d₂], D₁ ∪ D₂)

// ... similar for other constructs
```

### 4.2 Dimension Unification

**Algorithm 4.2 (Dimension Unification).**

Dimension constraints are linear equations over dimension vectors. We solve using Gaussian elimination.

```
unify_dim(d₁, d₂) =
    // d₁, d₂ are dimension expressions possibly containing variables
    // Convert to vectors and solve d₁ - d₂ = 0
    let eq = to_vector(d₁) - to_vector(d₂) in
    gaussian_eliminate(eq)
```

**Theorem 4.1 (Dimension Unification Decidability).** Dimension unification is decidable in O(n³) time where n is the number of dimension variables.

*Proof:* Dimension constraints are linear equations over integers. Gaussian elimination with integer arithmetic terminates and decides satisfiability. □

### 4.3 Soundness and Completeness

**Theorem 4.2 (Soundness of W).** If `W(Γ, e) = (S, τ, D)` and `D` is satisfiable, then `S(Γ) ⊢ e : τ`.

*Proof:* By induction on `e`. Each case follows from the corresponding typing rule. □

**Theorem 4.3 (Completeness of W).** If `Γ ⊢ e : τ`, then `W(Γ', e) = (S, τ', D)` for some `Γ' ⊆ Γ`, `S`, `τ'`, `D` where `τ = S'(τ')` for some substitution `S'`.

*Proof:* By induction on the typing derivation. Principal type property follows from most general unifiers. □

**Theorem 4.4 (Principal Types).** Every typeable expression has a principal (most general) type.

*Proof:* Algorithm W computes most general unifiers; dimension constraints have principal solutions. □

### 4.4 Complexity

**Theorem 4.5 (Inference Complexity).** Type inference runs in O(n² · m³) time where n is expression size and m is the number of dimension variables.

*Proof:*
- Standard HM inference: O(n²) with efficient union-find
- Dimension constraint solving: O(m³) Gaussian elimination
- Combined: O(n² · m³) □

---

## 5. Operational Semantics Properties

### 5.1 Evaluation Contexts

**Definition 5.1 (Evaluation Context).** An evaluation context `E` is an expression with a hole `□`:
```
E ::= □
    | E e | v E
    | let x = E in e
    | if E then e₁ else e₂
    | (E, e) | (v, E)
    | fst E | snd E
    | inl E | inr E
    | match E with inl x => e₁ | inr y => e₂
    | E + e | v + E
    | E * e | v * E
    | E / e | v / E
```

**Definition 5.2 (Context Application).** `E[e]` denotes filling hole `□` with expression `e`.

### 5.2 Congruence

**Lemma 5.1 (Congruence).** If `e ⟶ e'`, then `E[e] ⟶ E[e']` for any evaluation context `E`.

*Proof:* By induction on the structure of `E`. Each case corresponds to a congruence rule in the operational semantics. □

### 5.3 Confluence

**Theorem 5.1 (Confluence).** The reduction relation `⟶` is confluent: if `e ⟶* e₁` and `e ⟶* e₂`, then there exists `e'` such that `e₁ ⟶* e'` and `e₂ ⟶* e'`.

*Proof:* By the diamond property. Eclexia has no overlapping redexes in the deterministic fragment. For adaptive blocks, solution selection is deterministic given fixed shadow prices. □

---

## 6. Resource Safety

We prove that well-typed programs never exceed their declared resource budgets.

### 6.1 Resource Semantics

**Definition 6.1 (Resource Configuration).** A configuration `⟨e, Σ, B⟩` consists of:
- Expression `e` to evaluate
- Resource state `Σ: R → ℝ≥0` (current consumption)
- Budget `B: R → ℝ≥0 ∪ {∞}` (maximum allowed)

**Definition 6.2 (Resource Reduction).** `⟨e, Σ, B⟩ ⟶ᵣ ⟨e', Σ', B⟩` extends the standard reduction with resource tracking:

```
                            e ⟶ e'    Σ' = Σ
────────────────────────────────────────────────  (R-Pure)
⟨e, Σ, B⟩ ⟶ᵣ ⟨e', Σ', B⟩


select(solutions, Σ, B, obj) = i    Σ' = Σ + provides(sᵢ)    Σ' ⊑ B
─────────────────────────────────────────────────────────────────────  (R-Adaptive)
⟨adaptive { solutions }, Σ, B⟩ ⟶ᵣ ⟨eᵢ, Σ', B⟩
```

### 6.2 Feasibility Invariant

**Definition 6.3 (Feasibility).** Configuration `⟨e, Σ, B⟩` is *feasible* iff `Σ ⊑ B`.

**Lemma 6.1 (Feasibility Preservation).** If `⟨e, Σ, B⟩` is feasible and `⟨e, Σ, B⟩ ⟶ᵣ ⟨e', Σ', B⟩`, then `⟨e', Σ', B⟩` is feasible.

*Proof:* By case analysis on the reduction rule.

**Case R-Pure:** `Σ' = Σ`, feasibility preserved trivially.

**Case R-Adaptive:** By premise, `Σ' ⊑ B`. ✓ □

### 6.3 Resource Safety Theorem

**Theorem 6.1 (Resource Safety).** If `⟨e, Σ₀, B⟩` is feasible and `⟨e, Σ₀, B⟩ ⟶ᵣ* ⟨v, Σₙ, B⟩`, then `Σₙ ⊑ B`.

*Proof:* By induction on the length of the reduction sequence, applying Lemma 6.1 at each step. □

**Corollary 6.1 (No Budget Violation).** A well-typed program never consumes more resources than its declared budget.

*Proof:* Budget constraints are checked in T-Adaptive; R-Adaptive only selects feasible solutions. By Resource Safety, all intermediate and final states satisfy `Σ ⊑ B`. □

### 6.4 Resource Leak Freedom

**Definition 6.4 (Resource Leak).** A resource leak occurs when resources are consumed but not accounted for.

**Theorem 6.2 (No Resource Leaks).** All resource consumption in Eclexia is explicitly tracked in `@provides` clauses.

*Proof:*
1. R-Pure rule doesn't modify `Σ` (pure computation is resource-free)
2. R-Adaptive rule adds exactly `provides(sᵢ)` to `Σ`
3. No other rules modify `Σ`

Therefore, `Σ` accurately reflects all resource consumption. □

---

## 7. Determinism

### 7.1 Solution Ordering

**Definition 7.1 (Solution Cost).** Given shadow prices `λ`, the cost of solution `s` is:
```
cost(s, λ) = Σᵣ λᵣ · provides(s, r)
```

**Definition 7.2 (Strict Ordering).** Solutions have *strict ordering* under `λ` if for all feasible `sᵢ ≠ sⱼ`:
```
cost(sᵢ, λ) ≠ cost(sⱼ, λ)
```

### 7.2 Determinism Theorem

**Theorem 7.1 (Determinism).** If solutions have strict ordering under shadow prices `λ`, then the reduction relation `⟶` is deterministic.

*Proof:*
1. Standard reductions (β, let, if, etc.) are deterministic by definition.
2. Adaptive selection uses `argmin`, which is unique under strict ordering.
3. All other constructs are standard and deterministic.

Therefore, given any `e`, there is at most one `e'` such that `e ⟶ e'`. □

### 7.3 Handling Ties

**Definition 7.3 (Tie-Breaking).** When multiple solutions have equal cost, we use lexicographic ordering by solution name.

**Theorem 7.2 (Total Ordering).** With tie-breaking, solution selection is always deterministic.

*Proof:* Solution names are unique strings; string comparison gives total order. Combined with cost comparison, we have lexicographic total order on (cost, name). □

---

## 8. Economic Optimality

We prove that shadow prices converge to economically optimal values.

### 8.1 Linear Programming Formulation

**Definition 8.1 (Resource Allocation LP).** Given remaining budget `b = B - Σ` and feasible solutions `S`, the allocation problem is:

```
(Primal)
minimize    c^T x
subject to  Ax ≤ b
            Σᵢ xᵢ = 1        (select exactly one)
            xᵢ ∈ {0, 1}      (binary selection)
```

where:
- `x ∈ {0,1}^n` is the selection vector
- `c ∈ ℝⁿ` is the objective coefficient vector
- `A ∈ ℝ^{m×n}` is the resource consumption matrix
- `b ∈ ℝᵐ` is the remaining budget vector

### 8.2 LP Duality

**Definition 8.2 (Dual LP).**
```
(Dual)
maximize    b^T λ
subject to  A^T λ ≥ c
            λ ≥ 0
```

**Theorem 8.1 (Strong Duality).** If Primal has optimal solution `x*`, then Dual has optimal solution `λ*` with equal objective value:
```
c^T x* = b^T λ*
```

*Proof:* Standard LP duality theory. □

### 8.3 Shadow Price Interpretation

**Theorem 8.2 (Shadow Price as Marginal Value).** The shadow price `λᵣ*` equals the marginal value of resource `r`:
```
λᵣ* = ∂OPT/∂bᵣ
```

where `OPT` is the optimal objective value.

*Proof:* By the envelope theorem for linear programs. □

**Theorem 8.3 (Complementary Slackness).**
1. If resource `r` is not binding (`Σᵢ aᵣᵢ xᵢ* < bᵣ`), then `λᵣ* = 0`.
2. If `λᵣ* > 0`, then resource `r` is binding (`Σᵢ aᵣᵢ xᵢ* = bᵣ`).

*Proof:* Standard complementary slackness conditions for LP. □

### 8.4 Convergence

**Theorem 8.4 (Shadow Price Convergence).** As the number of adaptive decisions increases, empirical shadow prices converge to true optimal shadow prices.

*Proof Sketch:*
1. Each adaptive selection solves an LP with current budget.
2. LP solutions are optimal for given constraints.
3. By law of large numbers, average resource consumption converges to expected value.
4. Shadow prices, computed from LP duals, converge to true marginal values. □

**TODO:** Formalize convergence rate bounds using concentration inequalities.

### 8.5 Multi-Objective Optimality

**Definition 8.3 (Pareto Optimality).** Solution `s` is *Pareto optimal* if no solution `s'` dominates it:
```
¬∃s'. (∀r. cost(s', r) ≤ cost(s, r)) ∧ (∃r. cost(s', r) < cost(s, r))
```

**Theorem 8.5 (Pareto Selection).** With appropriate weight scalarization, Eclexia's selection produces Pareto-optimal solutions.

*Proof:* Weighted sum scalarization with positive weights always yields Pareto-optimal points (standard result in multi-objective optimization). □

---

## 9. Termination

### 9.1 Termination Under Resource Bounds

**Theorem 9.1 (Bounded Termination).** If budget `B` is finite and each non-value reduction consumes positive resources, then evaluation terminates.

*Proof:*
1. Define potential `Φ(Σ) = Σᵣ (B(r) - Σ(r))` (total slack).
2. Each R-Adaptive step decreases `Φ` by at least `min_cost > 0`.
3. `Φ ≥ 0` at all times (by Resource Safety).
4. Therefore, at most `Φ(Σ₀) / min_cost` adaptive steps can occur.
5. Between adaptive steps, only finitely many pure steps (by strong normalization of simply-typed λ-calculus with extensions). □

### 9.2 Strong Normalization

**Definition 9.1 (Termination Measure).** We define a lexicographic measure:
```
μ(e, Σ, B) = (Φ(Σ), size(e))
```

where `Φ(Σ) = Σᵣ (B(r) - Σ(r))` and `size(e)` is the AST size.

**Theorem 9.2 (Well-Founded Measure).** The measure `μ` is well-founded under lexicographic ordering, and every reduction step strictly decreases `μ`.

*Proof:*
- R-Adaptive: `Φ` decreases (first component)
- R-Pure: `Φ` unchanged, `size(e')` decreases (standard β-reduction shrinks term under CBV) □

**TODO:** Prove strong normalization for the pure fragment using logical relations or reducibility candidates.

### 9.3 Non-Termination Detection

**Theorem 9.3 (Termination Check).** Given finite budget `B` and explicit resource costs, termination is decidable.

*Proof Sketch:*
1. Maximum number of adaptive selections is bounded by `|B| / min_provides`.
2. Pure fragment (STLC + sums + products) is strongly normalizing.
3. Composition is decidable. □

**TODO:** Implement termination checker in type system.

---

## 10. Soundness of Constraint Solving

### 10.1 Constraint Language

**Definition 10.1 (Resource Constraint).** A resource constraint has the form:
```
C ::= resource op expr
    | C₁ ∧ C₂
    | true
```

where `op ∈ {<, ≤, >, ≥, =}`.

### 10.2 Constraint Satisfaction

**Definition 10.2 (Constraint Satisfaction).** Environment `E` satisfies constraint `C`, written `E ⊨ C`:
```
E ⊨ true                          always
E ⊨ r op n                        iff E(r) op n
E ⊨ C₁ ∧ C₂                       iff E ⊨ C₁ and E ⊨ C₂
```

### 10.3 Constraint Propagation Soundness

**Theorem 10.1 (Propagation Soundness).** If constraint propagation derives `C'` from `C`, then `C' ⊆ C` (every solution of `C` is a solution of `C'`).

*Proof:* Propagation rules are sound transformations:
- Interval narrowing preserves solutions
- Bounds propagation is monotonic
- No solution is lost □

### 10.4 Feasibility Detection

**Theorem 10.2 (Infeasibility Detection).** If `@requires C` and `@provides P` are inconsistent, the type checker rejects the program.

*Proof:*
1. Type checking collects constraints from `@requires` and `@provides`.
2. LP solver checks feasibility: `∃x. Ax ≤ b`.
3. Infeasible LP → no valid solution exists → type error. □

---

## 11. Metatheoretic Properties

### 11.1 Subject Reduction

**Theorem 11.1 (Subject Reduction).** Types are preserved under reduction:
```
Γ ⊢ e : τ ∧ e ⟶ e' ⟹ Γ ⊢ e' : τ
```

*Proof:* Preservation theorem (Theorem 2.2). □

### 11.2 Type Soundness

**Theorem 11.2 (Type Soundness).** Well-typed programs don't go wrong:
```
∅ ⊢ e : τ ⟹ e ↛ stuck
```

where `stuck` means neither a value nor reducible (and not resource exhaustion).

*Proof:* By Progress (Theorem 2.1) and Preservation (Theorem 2.2). □

### 11.3 Parametricity

**Theorem 11.3 (Parametricity).** Polymorphic functions are parametric: they cannot inspect their type parameters.

*Proof Sketch:* Standard parametricity argument via logical relations. Resource types don't break parametricity as they're orthogonal to the polymorphic structure. □

**TODO:** Full parametricity proof via logical relations.

### 11.4 Coherence

**Theorem 11.4 (Coherence).** Type inference produces semantically equivalent programs regardless of inference path.

*Proof:* Principal type property ensures unique (most general) typing. □

### 11.5 Decidability Summary

| Property | Decidable | Complexity |
|----------|-----------|------------|
| Type checking | Yes | O(n²) |
| Type inference | Yes | O(n² · m³) |
| Dimension checking | Yes | O(m³) |
| Constraint satisfaction | Yes | Polynomial (LP) |
| Termination (bounded) | Yes | Decidable |
| Termination (general) | No | Undecidable |

---

## Appendix A: Proof Mechanization

### A.1 Coq Formalization Status

**TODO:** Mechanize proofs in Coq.

Planned structure:
```coq
(* Syntax *)
Inductive expr : Type := ...
Inductive type : Type := ...
Inductive dim : Type := ...

(* Typing *)
Inductive has_type : ctx -> expr -> type -> Prop := ...

(* Semantics *)
Inductive step : expr -> expr -> Prop := ...

(* Safety *)
Theorem progress : forall e T,
  has_type empty e T ->
  value e \/ exists e', step e e'.

Theorem preservation : forall e e' T,
  has_type empty e T ->
  step e e' ->
  has_type empty e' T.
```

### A.2 Lean 4 Formalization Status

**TODO:** Port proofs to Lean 4 using Mathlib.

### A.3 Agda Formalization Status

**TODO:** Formalize in Agda for pedagogical presentation.

---

## Appendix B: Extended Proofs

### B.1 Full Substitution Lemma Proof

*[Detailed case-by-case proof for all expression forms]*

**TODO:** Complete all cases systematically.

### B.2 Full Progress Proof

*[All cases including resource operations and adaptive blocks]*

**TODO:** Complete all cases systematically.

### B.3 Full Preservation Proof

*[All cases including resource operations and adaptive blocks]*

**TODO:** Complete all cases systematically.

---

## Appendix C: Auxiliary Lemmas

### C.1 Weakening

**Lemma C.1 (Weakening).** If `Γ ⊢ e : τ` and `x ∉ dom(Γ)`, then `Γ, x:σ ⊢ e : τ`.

*Proof:* By induction on the typing derivation. □

### C.2 Exchange

**Lemma C.2 (Exchange).** If `Γ, x:σ, y:ρ, Δ ⊢ e : τ`, then `Γ, y:ρ, x:σ, Δ ⊢ e : τ`.

*Proof:* By induction on the typing derivation. □

### C.3 Contraction (for non-linear types)

**Lemma C.3 (Contraction).** If `Γ, x:τ, y:τ ⊢ e : σ` and `τ` is non-linear, then `Γ, z:τ ⊢ e[x,y := z] : σ`.

*Proof:* By induction on the typing derivation. □

---

## References

[1] Wright, A.K., Felleisen, M. "A Syntactic Approach to Type Soundness." Information and Computation 115.1 (1994): 38-94.

[2] Pierce, B.C. Types and Programming Languages. MIT Press, 2002.

[3] Harper, R. Practical Foundations for Programming Languages. Cambridge University Press, 2016.

[4] Dantzig, G.B. "Linear Programming and Extensions." Princeton University Press, 1963.

[5] Kennedy, A. "Dimension Types." ESOP 1994: 348-362.

[6] Cardelli, L. "Type Systems." ACM Computing Surveys 28.1 (1996): 263-264.

[7] Wadler, P., Blott, S. "How to Make Ad-hoc Polymorphism Less Ad Hoc." POPL 1989: 60-76.

[8] Reynolds, J.C. "Types, Abstraction and Parametric Polymorphism." IFIP 1983.

---

**Document Version:** 1.0
**Last Updated:** December 2025
**License:** PMPL-1.0-or-later

```bibtex
@techreport{eclexia2025proofs,
  title={Formal Proofs for Eclexia},
  author={Jewell, Jonathan D.A.},
  year={2025},
  month={December},
  institution={Eclexia Project},
  url={https://eclexia.org/proofs},
  note={Version 1.0}
}
```
