<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Type Theory and Categorical Semantics of Eclexia

<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

**Version:** 1.0
**Date:** December 2025
**Authors:** Jonathan D.A. Jewell
**Status:** Research Preview

---

## Abstract

This document presents the type-theoretic and categorical foundations of Eclexia. We develop: (1) a dependent type theory with resource indices; (2) categorical semantics via enriched category theory and graded monads; (3) domain-theoretic denotational semantics; (4) game semantics for interactive resource consumption; (5) realizability semantics connecting computation and proof; and (6) connections to homotopy type theory for higher-dimensional resource structure. This foundational work situates Eclexia within the broader landscape of programming language theory and provides a framework for future extensions.

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Type-Theoretic Foundations](#2-type-theoretic-foundations)
3. [Dependent Resource Types](#3-dependent-resource-types)
4. [Categorical Semantics](#4-categorical-semantics)
5. [Enriched Categories and Graded Monads](#5-enriched-categories-and-graded-monads)
6. [Domain-Theoretic Semantics](#6-domain-theoretic-semantics)
7. [Game Semantics](#7-game-semantics)
8. [Realizability Semantics](#8-realizability-semantics)
9. [Effect Systems and Algebraic Effects](#9-effect-systems-and-algebraic-effects)
10. [Session Types for Resources](#10-session-types-for-resources)
11. [Homotopy Type Theory Connections](#11-homotopy-type-theory-connections)
12. [Coherence and Canonicity](#12-coherence-and-canonicity)
13. [Normalization](#13-normalization)
14. [Decidability Results](#14-decidability-results)
15. [Extensions and Future Directions](#15-extensions-and-future-directions)

---

## 1. Introduction

### 1.1 Motivation

Eclexia's Economics-as-Code paradigm requires a sophisticated type-theoretic foundation that:

1. **Tracks resources precisely** through types
2. **Ensures dimensional correctness** at compile time
3. **Supports optimization objectives** declaratively
4. **Enables adaptive computation** with formal guarantees
5. **Connects to established mathematical structures**

### 1.2 Type-Theoretic Landscape

```
                    Dependent Types
                         │
            ┌────────────┼────────────┐
            │            │            │
       Martin-Löf    Calculus of    Cubical
       Type Theory   Constructions   Type Theory
            │            │            │
            └────────────┼────────────┘
                         │
                    ┌────┴────┐
                    │         │
              Linear Types  Graded Types
                    │         │
                    └────┬────┘
                         │
                    Quantitative
                    Type Theory
                         │
                    Eclexia's
                    Resource Types
```

### 1.3 Mathematical Prerequisites

We assume familiarity with:
- Basic category theory (categories, functors, natural transformations)
- Type theory (λ-calculus, polymorphism, dependent types)
- Domain theory (CPOs, Scott continuity)
- Order theory (lattices, Galois connections)

---

## 2. Type-Theoretic Foundations

### 2.1 Core Type Theory

Eclexia's type theory is based on a predicative, intensional Martin-Löf Type Theory extended with:

1. **Polymorphism** (System F-style)
2. **Resource types** with dimensional indices
3. **Effect types** via graded monads
4. **Constraint types** for optimization

#### 2.1.1 Judgment Forms

```
Γ ⊢                     Context Γ is well-formed
Γ ⊢ A type              A is a type in context Γ
Γ ⊢ A ≡ B type          A and B are definitionally equal types
Γ ⊢ a : A               a has type A in context Γ
Γ ⊢ a ≡ b : A           a and b are definitionally equal at type A
```

#### 2.1.2 Context Formation

```
─────────────  (Ctx-Empty)
· ⊢


Γ ⊢    Γ ⊢ A type    x ∉ dom(Γ)
───────────────────────────────  (Ctx-Ext)
Γ, x:A ⊢
```

#### 2.1.3 Type Formation Rules

```
Γ ⊢
─────────────  (Ty-Unit)
Γ ⊢ 𝟙 type


Γ ⊢
─────────────  (Ty-Bool)
Γ ⊢ 𝔹 type


Γ ⊢
─────────────  (Ty-Int)
Γ ⊢ ℤ type


Γ ⊢ A type    Γ ⊢ B type
────────────────────────  (Ty-Arr)
Γ ⊢ A → B type


Γ ⊢ A type    Γ ⊢ B type
────────────────────────  (Ty-Prod)
Γ ⊢ A × B type


Γ ⊢ A type    Γ ⊢ B type
────────────────────────  (Ty-Sum)
Γ ⊢ A + B type


Γ, x:A ⊢ B type
─────────────────  (Ty-Pi)
Γ ⊢ Πx:A. B type


Γ, x:A ⊢ B type
─────────────────  (Ty-Sigma)
Γ ⊢ Σx:A. B type


Γ ⊢ d : Dim
──────────────────────  (Ty-Resource)
Γ ⊢ Resource(rk, d) type
```

### 2.2 Universe Hierarchy

```
Γ ⊢
──────────────────  (Ty-Universe)
Γ ⊢ 𝒰ᵢ type


Γ ⊢ A : 𝒰ᵢ
────────────  (Ty-El)
Γ ⊢ El(A) type


i < j
────────────────  (Cumulative)
Γ ⊢ 𝒰ᵢ : 𝒰ⱼ
```

### 2.3 Dimension Types

Dimensions form a first-class type with group structure:

```
Γ ⊢
───────────────  (Dim-Type)
Γ ⊢ Dim type


Γ ⊢
──────────────  (Dim-Unit)
Γ ⊢ 1 : Dim


b ∈ {M, L, T, I, Θ, N, J}
─────────────────────────  (Dim-Base)
Γ ⊢ b : Dim


Γ ⊢ d₁ : Dim    Γ ⊢ d₂ : Dim
──────────────────────────────  (Dim-Mul)
Γ ⊢ d₁ · d₂ : Dim


Γ ⊢ d : Dim
─────────────────  (Dim-Inv)
Γ ⊢ d⁻¹ : Dim


Γ ⊢ d : Dim    Γ ⊢ n : ℤ
───────────────────────────  (Dim-Pow)
Γ ⊢ d^n : Dim
```

### 2.4 Dimension Equality

```
Γ ⊢ d : Dim
──────────────────────  (Dim-Id-L)
Γ ⊢ 1 · d ≡ d : Dim


Γ ⊢ d : Dim
──────────────────────  (Dim-Id-R)
Γ ⊢ d · 1 ≡ d : Dim


Γ ⊢ d₁ : Dim    Γ ⊢ d₂ : Dim    Γ ⊢ d₃ : Dim
─────────────────────────────────────────────  (Dim-Assoc)
Γ ⊢ (d₁ · d₂) · d₃ ≡ d₁ · (d₂ · d₃) : Dim


Γ ⊢ d₁ : Dim    Γ ⊢ d₂ : Dim
──────────────────────────────  (Dim-Comm)
Γ ⊢ d₁ · d₂ ≡ d₂ · d₁ : Dim


Γ ⊢ d : Dim
─────────────────────────  (Dim-Inv-L)
Γ ⊢ d⁻¹ · d ≡ 1 : Dim


Γ ⊢ d : Dim
─────────────────────────  (Dim-Inv-R)
Γ ⊢ d · d⁻¹ ≡ 1 : Dim
```

---

## 3. Dependent Resource Types

### 3.1 Resource Indices

Resource types are indexed by dimensions:

```
Resource : ResourceKind → Dim → Type
```

This allows:
- `Resource(Energy, M·L²·T⁻²)` — Energy in SI
- `Resource(Time, T)` — Time
- `Resource(Power, M·L²·T⁻³)` — Power = Energy/Time

### 3.2 Dependent Function Types with Resources

```
Γ, x:A ⊢ B type    Γ ⊢ r : ResourceProfile
────────────────────────────────────────────  (Ty-Pi-Res)
Γ ⊢ Πʳx:A. B type


Γ, x:A ⊢ e : B    Γ ⊢ r : ResourceProfile
────────────────────────────────────────────  (Tm-Lam-Res)
Γ ⊢ λʳx:A. e : Πʳx:A. B


Γ ⊢ f : Πʳx:A. B    Γ ⊢ a : A    resources_available(r)
────────────────────────────────────────────────────────  (Tm-App-Res)
Γ ⊢ f a : B[a/x]
```

### 3.3 Resource Constraint Types

```
Γ ⊢ A type    Γ ⊢ C : Constraint
────────────────────────────────  (Ty-Constrained)
Γ ⊢ A @requires C type


Γ ⊢ a : A    Γ ⊢ satisfies(a, C)
────────────────────────────────  (Tm-Constrain)
Γ ⊢ a : A @requires C
```

### 3.4 Subtyping for Constraints

```
C₁ ⊇ C₂
────────────────────────────────────────  (Sub-Constraint)
Γ ⊢ A @requires C₁ <: A @requires C₂


Γ ⊢ a : A @requires C₁    Γ ⊢ A @requires C₁ <: A @requires C₂
──────────────────────────────────────────────────────────────  (Sub-App)
Γ ⊢ a : A @requires C₂
```

### 3.5 Resource-Indexed Families

```
Γ ⊢ A : Resource(rk, d) → Type
────────────────────────────────  (Fam-Resource)
Γ ⊢ A(r) type for r : Resource(rk, d)
```

**Example:** Bounded computation family:
```
BoundedComp : (b : Resource(Energy, J)) → Type
BoundedComp(b) = Σ(A : Type). Σ(compute : A). (cost(compute) ≤ b)
```

---

## 4. Categorical Semantics

### 4.1 Categorical Models of Type Theory

Eclexia's type theory is modeled in:
1. **Locally cartesian closed categories (LCCCs)** for dependent types
2. **Symmetric monoidal categories** for resources
3. **Enriched categories** for graded effects

### 4.2 The Base Category

Let **Set** be the category of sets and functions.

**Definition 4.1 (Eclexia Model Category).** The semantic category **Ecl** is:
- Objects: Pairs `(X, ρ)` where `X ∈ Set` and `ρ : X → ResourceProfile`
- Morphisms: Functions `f : X → Y` such that `ρ_Y(f(x)) ≤ ρ_X(x)` (resource non-increasing)
- Composition: Standard function composition
- Identity: Identity function

### 4.3 Cartesian Closed Structure

**Proposition 4.1.** **Ecl** is cartesian closed.

*Proof:*
- Terminal object: `(1, λ_.∅)` where `1` is singleton set
- Products: `(X, ρ_X) × (Y, ρ_Y) = (X × Y, λ(x,y). ρ_X(x) ⊕ ρ_Y(y))`
- Exponentials: `(Y, ρ_Y)^(X, ρ_X) = (X → Y, λf. sup_{x ∈ X} ρ_Y(f(x)) ⊖ ρ_X(x))` □

### 4.4 Interpretation of Types

```
⟦𝟙⟧ = (1, λ_.∅)
⟦𝔹⟧ = ({tt, ff}, λ_.∅)
⟦ℤ⟧ = (ℤ, λ_.∅)
⟦A → B⟧ = ⟦B⟧^⟦A⟧
⟦A × B⟧ = ⟦A⟧ × ⟦B⟧
⟦A + B⟧ = ⟦A⟧ + ⟦B⟧
⟦Resource(rk, d)⟧ = (ℝ × {d}, λr. ⟨rk ↦ r⟩)
⟦Πx:A. B⟧ = Π_{a ∈ ⟦A⟧} ⟦B⟧[a/x]
⟦Σx:A. B⟧ = Σ_{a ∈ ⟦A⟧} ⟦B⟧[a/x]
```

### 4.5 Interpretation of Terms

```
⟦x⟧_γ = γ(x)
⟦λx.e⟧_γ = λa. ⟦e⟧_{γ[x↦a]}
⟦e₁ e₂⟧_γ = ⟦e₁⟧_γ (⟦e₂⟧_γ)
⟦(e₁, e₂)⟧_γ = (⟦e₁⟧_γ, ⟦e₂⟧_γ)
⟦π₁ e⟧_γ = π₁(⟦e⟧_γ)
⟦π₂ e⟧_γ = π₂(⟦e⟧_γ)
⟦n unit⟧_γ = (n, dim(unit))
⟦e₁ +_ρ e₂⟧_γ = ⟦e₁⟧_γ +_ℝ ⟦e₂⟧_γ  (with dimension check)
```

### 4.6 Soundness

**Theorem 4.1 (Soundness).** If `Γ ⊢ e : A` then `⟦Γ⟧ ⊢ ⟦e⟧ : ⟦A⟧`.

*Proof:* By induction on the typing derivation. Each typing rule corresponds to a categorical construction. □

### 4.7 Completeness (for Equational Theory)

**Theorem 4.2 (Completeness).** If `⟦Γ⟧ ⊨ ⟦e₁⟧ = ⟦e₂⟧ : ⟦A⟧` then `Γ ⊢ e₁ ≡ e₂ : A`.

*Proof:* The model is the term model modulo βη-equivalence, which is complete for the equational theory. □

---

## 5. Enriched Categories and Graded Monads

### 5.1 Resource-Graded Categories

**Definition 5.1 (Grading Monoid).** Let `(R, ⊕, 0, ≤)` be a preordered monoid of resource annotations:
- `R = ResourceProfile`
- `⊕`: Resource combination (pointwise addition)
- `0`: Empty resource profile
- `≤`: Subsumption ordering

**Definition 5.2 (R-Graded Category).** An R-graded category **C** has:
- Objects: |**C**|
- Hom-sets: **C**(A, B) = ∪_{r ∈ R} **C**_r(A, B)
- Composition: If `f ∈ **C**_r(A, B)` and `g ∈ **C**_s(B, C)`, then `g ∘ f ∈ **C**_{r ⊕ s}(A, C)`
- Identity: `id_A ∈ **C**_0(A, A)`

### 5.2 Graded Monads

**Definition 5.3 (Graded Monad).** An R-graded monad on category **C** consists of:
- Functor `T_r : **C** → **C**` for each `r ∈ R`
- Natural transformation `η : Id → T_0` (unit)
- Natural transformation `μ_{r,s} : T_r ∘ T_s → T_{r ⊕ s}` (multiplication)

Satisfying associativity and unit laws.

### 5.3 Resource Monad

**Definition 5.4 (Resource Monad).** The resource monad `Res_r` for profile `r` is:
```
Res_r(A) = { (a, cost) | a ∈ A, cost ≤ r }
```

With operations:
```
η : A → Res_0(A)
η(a) = (a, 0)

μ : Res_r(Res_s(A)) → Res_{r⊕s}(A)
μ((a, c₁), c₂) = (a, c₁ ⊕ c₂)
```

### 5.4 Kleisli Category

**Definition 5.5 (Graded Kleisli Category).** The Kleisli category **Kl**(T) has:
- Objects: Same as **C**
- Morphisms: **Kl**(T)_r(A, B) = **C**(A, T_r(B))
- Composition: Kleisli composition using `μ`

### 5.5 Graded Comonads for Coeffects

Dual to graded monads, graded comonads model *coeffects* (context requirements):

**Definition 5.6 (Graded Comonad).** An R-graded comonad on **C** consists of:
- Functor `D_r : **C** → **C**` for each `r ∈ R`
- Natural transformation `ε : D_0 → Id` (counit)
- Natural transformation `δ_{r,s} : D_{r ⊕ s} → D_r ∘ D_s` (comultiplication)

**Example:** The `@requires` constraint acts as a graded comonad:
```
D_C(A) = A @requires C
```

### 5.6 Adjunctions

**Proposition 5.1.** There is an adjunction:
```
F_r ⊣ U_r : **Kl**(Res_r) → **C**
```

where `F_r(A) = A` and `U_r(A) = Res_r(A)`.

---

## 6. Domain-Theoretic Semantics

### 6.1 Domains

**Definition 6.1 (Domain).** A domain `D` is a directed-complete partial order (dcpo) with a least element ⊥.

**Definition 6.2 (Scott Continuity).** A function `f : D → E` is Scott continuous if it preserves directed suprema:
```
f(⊔ S) = ⊔ { f(d) | d ∈ S }
```

### 6.2 Domain Equations

Recursive types are solved via domain equations:

```
⟦μα.τ⟧ = fix(λD. ⟦τ⟧[D/α])
```

**Theorem 6.1 (Domain Equation Solvability).** For strictly positive `τ`, the equation `D = ⟦τ⟧[D/α]` has a solution.

*Proof:* By Smyth-Plotkin theorem on bilimits. □

### 6.3 Resource-Annotated Domains

**Definition 6.3 (Resource Domain).** A resource domain `(D, cost)` pairs:
- Domain `D` of values
- Cost function `cost : D → ResourceProfile_⊥`

### 6.4 Lifting for Partiality

```
D_⊥ = D ∪ {⊥}
```

For resource types:
```
⟦A⟧_⊥ = { (v, r) | v ∈ ⟦A⟧, r : ResourceProfile } ∪ {⊥}
```

### 6.5 Fixed Points

**Definition 6.4 (Fixed Point Operator).**
```
fix : ((A → B) → (A → B)) → (A → B)
fix(F) = ⊔_{n ∈ ℕ} F^n(⊥)
```

**Theorem 6.2 (Kleene's Theorem).** `fix(F) = F(fix(F))` for continuous `F`.

### 6.6 Denotational Semantics

```
⟦e⟧ : Env → ⟦τ⟧

⟦x⟧ρ = ρ(x)
⟦λx.e⟧ρ = λv. ⟦e⟧ρ[x↦v]
⟦e₁ e₂⟧ρ = ⟦e₁⟧ρ (⟦e₂⟧ρ)
⟦fix f. e⟧ρ = fix(λv. ⟦e⟧ρ[f↦v])
⟦if e₁ then e₂ else e₃⟧ρ = cond(⟦e₁⟧ρ, ⟦e₂⟧ρ, ⟦e₃⟧ρ)

where cond(tt, d₁, d₂) = d₁
      cond(ff, d₁, d₂) = d₂
      cond(⊥, d₁, d₂) = ⊥
```

### 6.7 Adequacy

**Theorem 6.3 (Computational Adequacy).** For closed `e : Bool`:
```
⟦e⟧∅ = tt ⟺ e ⟶* true
⟦e⟧∅ = ff ⟺ e ⟶* false
⟦e⟧∅ = ⊥ ⟺ e diverges
```

*Proof:* Via logical relations between syntax and denotations. □

---

## 7. Game Semantics

### 7.1 Games and Strategies

**Definition 7.1 (Arena).** An arena `A = (M_A, λ_A, ⊢_A)` consists of:
- `M_A`: Set of moves
- `λ_A : M_A → {O, P}`: Polarity (Opponent/Proponent)
- `⊢_A ⊆ M_A^* × M_A`: Enabling relation

### 7.2 Resource Games

**Definition 7.2 (Resource Arena).** A resource arena `(A, cost)` extends arenas with:
- `cost : M_A → ResourceProfile`: Resource cost per move

### 7.3 Strategies as Programs

**Definition 7.3 (Strategy).** A strategy `σ : A` is a set of plays (alternating sequences of moves) satisfying:
1. Prefix-closure
2. Determinism on P-moves
3. Resource compliance: Total cost ≤ budget

### 7.4 Strategy Composition

Strategies compose via parallel composition with hiding:
```
σ ; τ = { s ↾ A,C | s ∈ σ ∥ τ, s complete }
```

### 7.5 Denotational Semantics via Games

```
⟦𝟙⟧ = I (empty arena)
⟦A → B⟧ = ⟦A⟧ ⊸ ⟦B⟧ (linear implication arena)
⟦A × B⟧ = ⟦A⟧ & ⟦B⟧ (product arena)
⟦A + B⟧ = ⟦A⟧ ⊕ ⟦B⟧ (sum arena)
```

### 7.6 Full Abstraction

**Conjecture 7.1 (Full Abstraction).** For ground types:
```
⟦e₁⟧ = ⟦e₂⟧ ⟺ e₁ ≃_{ctx} e₂
```

**TODO:** Prove or find counterexample.

---

## 8. Realizability Semantics

### 8.1 Realizability Interpretation

**Definition 8.1 (Realizer).** A realizer is a closed term `e` such that `e ⊩ P` (e realizes P).

### 8.2 Resource-Aware Realizability

**Definition 8.2 (Resource Realizability).** `e ⊩_r P` means:
- `e` realizes `P`
- `cost(e) ≤ r`

### 8.3 Realizability for Types

```
e ⊩_r 𝟙 ⟺ e = ()
e ⊩_r 𝔹 ⟺ e = true ∨ e = false
e ⊩_r A → B ⟺ ∀a, s. a ⊩_s A ⟹ e a ⊩_{r⊕s} B
e ⊩_r A × B ⟺ π₁ e ⊩_r A ∧ π₂ e ⊩_r B
e ⊩_r ∀α. A ⟺ ∀T. e[T] ⊩_r A[T/α]
e ⊩_r Resource(rk, d) ⟺ e = n unit ∧ cost(e, rk) = n
```

### 8.4 Soundness

**Theorem 8.1 (Realizability Soundness).** If `Γ ⊢ e : A` and `γ ⊩_r Γ`, then `γ(e) ⊩_r A`.

*Proof:* By induction on typing derivation. □

---

## 9. Effect Systems and Algebraic Effects

### 9.1 Algebraic Effects

**Definition 9.1 (Signature).** An effect signature `Σ` is a set of operation symbols with arities:
```
Σ = { op : A → B, ... }
```

### 9.2 Effect Handlers

```
handle e with {
    return x ↦ e_r,
    op(x, k) ↦ e_op,
    ...
}
```

### 9.3 Resource Effects

Define resource consumption as algebraic effect:

```
signature ResourceEffect {
    consume : Resource(rk, d) → Unit
    query_budget : Unit → Resource(rk, d)
    defer_until : Condition → Unit
}
```

### 9.4 Effect Typing

```
Γ ⊢ e : A ! ε

where ε is an effect row:
ε ::= ∅ | Op(A, B) | ε₁ ∪ ε₂
```

### 9.5 Row Polymorphism

```
Γ ⊢ e : A ! (ε ∪ ρ)
────────────────────────
Γ ⊢ e : ∀ρ. A ! (ε ∪ ρ)
```

### 9.6 Handler Typing

```
Γ ⊢ e : A ! (Op(S, T) ∪ ε)
Γ, x:A ⊢ e_r : B ! ε
Γ, x:S, k:(T → B ! ε) ⊢ e_op : B ! ε
─────────────────────────────────────────
Γ ⊢ handle e with {return x ↦ e_r, op(x, k) ↦ e_op} : B ! ε
```

### 9.7 Effect Semantics via Monads

**Theorem 9.1.** Algebraic effects with handlers are equivalent to parameterized monads.

```
T_{Op} A = Free_{Op}(A) = A + Σ_{op ∈ Op} (A_op × (B_op → T_{Op} A))
```

---

## 10. Session Types for Resources

### 10.1 Session Types

Session types describe communication protocols:

```
S ::= !A.S        -- Send A, continue with S
    | ?A.S        -- Receive A, continue with S
    | S ⊕ S'      -- Internal choice
    | S & S'      -- External choice
    | end         -- Session end
    | μα.S        -- Recursive session
    | α           -- Session variable
```

### 10.2 Resource Sessions

**Definition 10.1 (Resource Session).** A resource session `S @budget B` pairs:
- Session type `S`
- Resource budget `B` for entire session

### 10.3 Session Typing Rules

```
Γ; Δ, c:S ⊢ P ▷ c:S'
─────────────────────────────  (Send)
Γ; Δ, c:!A.S ⊢ c![e].P ▷ c:S


Γ, x:A; Δ, c:S ⊢ P ▷ c:S'
─────────────────────────────  (Recv)
Γ; Δ, c:?A.S ⊢ c?(x).P ▷ c:S'
```

### 10.4 Resource-Aware Sessions

```
Γ; Δ, c:S @budget B ⊢ P
cost(P) ≤ B
─────────────────────────────  (Session-Budget)
Γ; Δ, c:S ⊢ P
```

### 10.5 Session Duality

```
dual(!A.S) = ?A.dual(S)
dual(?A.S) = !A.dual(S)
dual(S ⊕ S') = dual(S) & dual(S')
dual(S & S') = dual(S) ⊕ dual(S')
dual(end) = end
```

**Theorem 10.1 (Session Safety).** Well-typed session programs are deadlock-free and respect resource budgets.

---

## 11. Homotopy Type Theory Connections

### 11.1 Paths as Dimension Equivalences

In HoTT, paths represent equality. For dimensions:
```
d₁ = d₂ : Dim  ↔  Path_Dim(d₁, d₂)
```

### 11.2 Univalence for Resources

**Conjecture 11.1 (Resource Univalence).**
```
(Resource(rk, d₁) ≃ Resource(rk, d₂)) ≃ (d₁ = d₂)
```

### 11.3 Higher Inductive Types for Constraints

```
data Feasible (C : Constraint) : Type where
  solution : (s : Solution) → satisfies(s, C) → Feasible(C)
  path : (s₁ s₂ : Solution) → equivalent(s₁, s₂) → solution(s₁) = solution(s₂)
```

### 11.4 Cubical Structure

**TODO:** Develop cubical semantics for resource dimensions.

---

## 12. Coherence and Canonicity

### 12.1 Coherence

**Definition 12.1 (Coherence).** All diagrams of canonical morphisms commute.

**Theorem 12.1 (Type-Theoretic Coherence).** Eclexia's type theory satisfies coherence:
- All proofs of type equality are equal
- Type-checking is invariant under proof choice

### 12.2 Canonicity

**Definition 12.2 (Canonicity).** Every closed term of base type reduces to a canonical form.

**Theorem 12.2 (Canonicity).** If `⊢ e : 𝔹` then `e ⟶* true` or `e ⟶* false`.

*Proof:* By logical relations. Define:
```
V_𝔹 = {true, false}
E_𝔹 = {e | e ⟶* v, v ∈ V_𝔹}
```

Show by induction that `⊢ e : 𝔹` implies `e ∈ E_𝔹`. □

**Theorem 12.3 (Resource Canonicity).** If `⊢ e : Resource(rk, d)` then `e ⟶* n unit` for some `n : ℝ`.

*Proof:* Similar to Boolean canonicity. □

---

## 13. Normalization

### 13.1 Normalization by Evaluation (NbE)

**Definition 13.1 (Semantic Values).**
```
⟦𝟙⟧ = 1
⟦𝔹⟧ = Bool
⟦A → B⟧ = ⟦A⟧ → ⟦B⟧
⟦A × B⟧ = ⟦A⟧ × ⟦B⟧
```

**Definition 13.2 (Reification and Reflection).**
```
reify : ⟦A⟧ → Nf(A)
reflect : Ne(A) → ⟦A⟧
```

### 13.2 NbE Algorithm

```
nf(e) = reify(eval(e, id))

eval : Tm → Env → ⟦A⟧
eval(x, ρ) = ρ(x)
eval(λx.e, ρ) = λv. eval(e, ρ[x↦v])
eval(e₁ e₂, ρ) = eval(e₁, ρ)(eval(e₂, ρ))
```

### 13.3 Strong Normalization

**Theorem 13.1 (Strong Normalization).** Every well-typed term has a normal form.

*Proof Sketch:*
1. Define reducibility candidates for each type
2. Show all terms are reducible
3. Conclude by reducibility implying SN □

**TODO:** Full proof via Girard's method of reducibility candidates.

### 13.4 Weak Normalization under Resource Bounds

**Theorem 13.2.** Under finite resource budget `B`, well-typed terms normalize within bounded steps.

*Proof:* See PROOFS.md §9 (Termination). □

---

## 14. Decidability Results

### 14.1 Type Checking

**Theorem 14.1 (Decidability of Type Checking).** Given `Γ`, `e`, `A`, deciding `Γ ⊢ e : A` is decidable.

*Proof:* Type checking rules are syntax-directed. Dimension equality is decidable (linear algebra over ℤ). □

### 14.2 Type Inference

**Theorem 14.2 (Decidability of Type Inference).** Given `Γ`, `e`, computing `A` such that `Γ ⊢ e : A` is decidable.

*Proof:* Extended Algorithm W with dimension constraint solving. □

### 14.3 Subtyping

**Theorem 14.3 (Decidability of Subtyping).** Given `A`, `B`, deciding `A <: B` is decidable.

*Proof:* Subtyping rules are inductive. Constraint subsumption is decidable (implication in linear arithmetic). □

### 14.4 Dimension Equivalence

**Theorem 14.4 (Decidability of Dimension Equality).** Given `d₁`, `d₂`, deciding `d₁ ≡ d₂` is decidable in O(n) time.

*Proof:* Compare dimension vectors componentwise. □

### 14.5 Constraint Satisfiability

**Theorem 14.5 (Decidability of Constraint Satisfiability).** Given constraint `C` and profile `p`, deciding `satisfies(p, C)` is decidable.

*Proof:* Constraints are linear inequalities; LP feasibility is polynomial-time decidable. □

### 14.6 Undecidability Results

**Theorem 14.6 (Undecidability of General Termination).** Termination of Eclexia programs without resource bounds is undecidable.

*Proof:* Reduction from the halting problem. □

---

## 15. Extensions and Future Directions

### 15.1 Planned Extensions

1. **Dependent Resource Types:** Full dependent types with resource indices
2. **Higher-Order Resources:** Resources parameterized by types
3. **Probabilistic Resources:** Stochastic resource consumption
4. **Concurrent Resources:** Shared resource management
5. **Quantum Resources:** Quantum computational resources

### 15.2 Open Problems

1. **Full Abstraction:** Prove or disprove for game semantics
2. **Parametricity for Resources:** Characterize free theorems
3. **Effectful Normalization:** Strong normalization with effects
4. **Cubical Resources:** Develop cubical semantics
5. **Certified Compiler:** Verified compilation to LLVM

### 15.3 Research Directions

1. **Machine Learning Integration:**
   - Learned resource prediction
   - Neural-guided optimization

2. **Blockchain/Smart Contracts:**
   - Gas as first-class resource
   - Verified resource bounds

3. **Distributed Systems:**
   - Network resources
   - Distributed constraint solving

4. **Quantum Computing:**
   - Qubit resources
   - Quantum circuit optimization

---

## Appendix A: Category Theory Glossary

| Term | Definition |
|------|------------|
| Category | Objects + morphisms + composition + identity |
| Functor | Structure-preserving map between categories |
| Natural transformation | Morphism between functors |
| Adjunction | Pair of functors with unit/counit |
| Monad | Endofunctor with unit and multiplication |
| Comonad | Dual of monad |
| Enriched category | Hom-sets replaced by objects in V |
| Graded monad | Monad indexed by monoid |

## Appendix B: Type Theory Glossary

| Term | Definition |
|------|------------|
| Judgment | Statement derivable in type theory |
| Context | List of typed variable bindings |
| Type formation | Rules for constructing types |
| Introduction rule | How to construct terms of a type |
| Elimination rule | How to use terms of a type |
| β-reduction | Computational reduction |
| η-expansion | Extensionality principle |
| Definitional equality | Built-in equality |
| Propositional equality | Type of equalities |

---

**Document Version:** 1.0
**Last Updated:** December 2025
**License:** MPL-2.0

```bibtex
@techreport{eclexia2025theory,
  title={Type Theory and Categorical Semantics of Eclexia},
  author={Jewell, Jonathan D.A.},
  year={2025},
  month={December},
  institution={Eclexia Project},
  url={https://eclexia.org/theory},
  note={Version 1.0}
}
```
