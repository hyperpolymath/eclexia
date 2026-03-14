# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Eclexia Type System Specification

**Version:** 1.0.0
**Date:** 2026-03-14
**Extracted from:** `eclexia-typeck/src/{lib,unify,infer,env,error}.rs`, `eclexia-ast/src/{types,dimension}.rs`

---

## 1. Type Language

### 1.1 Types

```
τ ::= Unit | Bool | Char | String                          primitive scalars
    | Int | I8 | I16 | I32 | I64 | I128                   signed integers
    | UInt | U8 | U16 | U32 | U64 | U128                  unsigned integers
    | Float | F32 | F64                                    floating-point
    | (τ₁, …, τₙ)                                          tuple
    | [τ; n?]                                              array (optionally sized)
    | τ₁ × … × τₙ → τᵣ                                    function type
    | N⟨τ₁, …, τₖ⟩                                         named type (struct/enum/alias)
    | Resource(P, D)                                       dimensioned resource
    | α                                                     type variable
    | ∀α₁…αₙ. τ                                            universal quantification
    | Never                                                 bottom type
    | Error                                                 error recovery type
```

### 1.2 Type Schemes

```
σ ::= ∀ᾱ. τ     where ᾱ = α₁, …, αₙ
```

A type scheme quantifies over free type variables. Monomorphic types have
ᾱ = ∅.

### 1.3 Type Aliases

```
Int  ≡ I64          (default integer width)
UInt ≡ U64
Float ≡ F64
```

---

## 2. Dimensional Type System

### 2.1 Dimension Space

Dimensions form an abelian group under multiplication with ten base exponents:

```
D = (mass, length, time, current, temperature, amount, luminosity, money, carbon, information)
  ∈ ℤ¹⁰

Operations:
  D₁ · D₂ = (d₁₁ + d₂₁, d₁₂ + d₂₂, …, d₁₁₀ + d₂₁₀)    multiplication
  D₁ / D₂ = (d₁₁ - d₂₁, d₁₂ - d₂₂, …, d₁₁₀ - d₂₁₀)    division
  D^n    = (n·d₁, n·d₂, …, n·d₁₀)                        exponentiation
  D⁻¹    = (-d₁, -d₂, …, -d₁₀)                           inverse
  1      = (0, 0, …, 0)                                    dimensionless
```

### 2.2 Derived Dimensions

| Name | Definition | SI |
|------|-----------|-----|
| Energy | mass¹ · length² · time⁻² | kg·m²·s⁻² = J |
| Power | mass¹ · length² · time⁻³ | kg·m²·s⁻³ = W |
| Force | mass¹ · length¹ · time⁻² | kg·m·s⁻² = N |
| Velocity | length¹ · time⁻¹ | m·s⁻¹ |
| Memory | information¹ | bit |
| Carbon | carbon¹ | gCO₂e |
| Carbon intensity | carbon¹ · energy⁻¹ | gCO₂e/J |

### 2.3 Dimensional Unification

```
    D₁ = D₂
    ────────────────────────────────────────────  [Dim-Unify]
    unify(Resource(P₁, D₁), Resource(P₂, D₂)) succeeds
    where P₁, P₂ unify as base primitives

    D₁ ≠ D₂
    ────────────────────────────────────────────────────  [Dim-Mismatch]
    unify(Resource(P₁, D₁), Resource(P₂, D₂))
    = DimensionMismatch(D₁, D₂)
```

### 2.4 Dimensional Arithmetic

```
    Γ ⊢ e₁ : Resource(P, D₁)     Γ ⊢ e₂ : Resource(P, D₂)
    D₁ = D₂
    ────────────────────────────────────────────────────  [Dim-Add]
    Γ ⊢ e₁ + e₂ : Resource(P, D₁)

    Γ ⊢ e₁ : Resource(P, D₁)     Γ ⊢ e₂ : Resource(P, D₂)
    ────────────────────────────────────────────────────  [Dim-Mul]
    Γ ⊢ e₁ * e₂ : Resource(P, D₁ · D₂)

    Γ ⊢ e₁ : Resource(P, D₁)     Γ ⊢ e₂ : Resource(P, D₂)
    ────────────────────────────────────────────────────  [Dim-Div]
    Γ ⊢ e₁ / e₂ : Resource(P, D₁ / D₂)
```

Addition requires matching dimensions; multiplication produces the product
dimension; division produces the quotient dimension.

---

## 3. Type Inference

Eclexia implements Algorithm W (Damas-Milner) with dimensional extensions.

### 3.1 Judgement Form

```
Γ ⊢ e : τ     (expression e has type τ under context Γ)
```

### 3.2 Typing Rules

**Literals:**

```
    ───────────────────  [T-Int]        ───────────────────  [T-Float]
    Γ ⊢ n : Int                        Γ ⊢ f : Float

    ───────────────────  [T-String]     ───────────────────  [T-Bool]
    Γ ⊢ s : String                     Γ ⊢ b : Bool

    ───────────────────  [T-Unit]       ───────────────────  [T-Char]
    Γ ⊢ () : Unit                      Γ ⊢ c : Char

    unit_dimension(u) = D
    ──────────────────────────────────  [T-Resource]
    Γ ⊢ vU : Resource(Float, D)        (e.g., 100J : Resource(Float, Energy))
```

**Variables:**

```
    (x : σ) ∈ Γ     τ = instantiate(σ)
    ──────────────────────────────────────  [T-Var]
    Γ ⊢ x : τ
```

**Lambda:**

```
    α₁, …, αₙ fresh     Γ, x₁: α₁, …, xₙ: αₙ ⊢ e : τ
    ────────────────────────────────────────────────────────  [T-Lambda]
    Γ ⊢ |x₁, …, xₙ| e : α₁ × … × αₙ → τ
```

**Application:**

```
    Γ ⊢ e₀ : τ₀     Γ ⊢ e₁ : τ₁ … Γ ⊢ eₙ : τₙ
    α fresh     unify(τ₀, τ₁ × … × τₙ → α)
    ──────────────────────────────────────────────  [T-App]
    Γ ⊢ e₀(e₁, …, eₙ) : α
```

**Let (with let-polymorphism):**

```
    Γ ⊢ e₁ : τ₁     σ = generalize(Γ, τ₁)     Γ, x: σ ⊢ e₂ : τ₂
    ──────────────────────────────────────────────────────────────────  [T-Let]
    Γ ⊢ let x = e₁; e₂ : τ₂
```

**If-Then-Else:**

```
    Γ ⊢ e_cond : Bool     Γ ⊢ e_then : τ₁     Γ ⊢ e_else : τ₂
    unify(τ₁, τ₂)
    ──────────────────────────────────────────────────────────────  [T-If]
    Γ ⊢ if e_cond { e_then } else { e_else } : τ₁
```

**Match:**

```
    Γ ⊢ e : τ_scrut
    ∀i: check_pattern(patᵢ, τ_scrut) = Γᵢ
        Γ ∪ Γᵢ ⊢ bodyᵢ : τᵢ
    unify(τ₁, …, τₙ)
    ──────────────────────────────────────────  [T-Match]
    Γ ⊢ match e { pat₁ => body₁, … } : τ₁
```

**Binary Operations:**

```
    Γ ⊢ e₁ : τ₁     Γ ⊢ e₂ : τ₂
    (τ₁, τ₂, ⊕) ∈ ArithRules     result = arith_result(τ₁, τ₂, ⊕)
    ──────────────────────────────────────────────────────────────  [T-BinOp]
    Γ ⊢ e₁ ⊕ e₂ : result
```

Arithmetic rules include:
- Int ⊕ Int → Int (for +, -, *, /, %)
- Float ⊕ Float → Float
- Int ⊕ Float → Float (implicit widening)
- String + String → String (concatenation)
- Comparisons → Bool

**Tuple:**

```
    ∀i. Γ ⊢ eᵢ : τᵢ
    ──────────────────────────────────  [T-Tuple]
    Γ ⊢ (e₁, …, eₙ) : (τ₁, …, τₙ)
```

**Array:**

```
    ∀i. Γ ⊢ eᵢ : τᵢ     unify(τ₁, …, τₙ)
    ────────────────────────────────────────  [T-Array]
    Γ ⊢ [e₁, …, eₙ] : [τ₁; n]
```

**Struct Construction:**

```
    N ∈ Γ.structs     fields(N) = {f₁: σ₁, …, fₙ: σₙ}
    ∀i. Γ ⊢ eᵢ : τᵢ     unify(τᵢ, instantiate(σᵢ))
    ──────────────────────────────────────────────────────  [T-Struct]
    Γ ⊢ N { f₁: e₁, …, fₙ: eₙ } : N
```

**Field Access:**

```
    Γ ⊢ e : N     fields(N) = {…, f: σ, …}
    ────────────────────────────────────────────  [T-Field]
    Γ ⊢ e.f : instantiate(σ)
```

**Method Call:**

```
    Γ ⊢ e : τ     methods(τ, m) = τ_self → τ₁ × … × τₙ → τᵣ
    unify(τ, τ_self)     ∀i. Γ ⊢ aᵢ : τ'ᵢ     unify(τ'ᵢ, τᵢ)
    ──────────────────────────────────────────────────────────────  [T-Method]
    Γ ⊢ e.m(a₁, …, aₙ) : τᵣ
```

**Type Cast:**

```
    Γ ⊢ e : τ₁     castable(τ₁, τ₂)
    ────────────────────────────────────  [T-Cast]
    Γ ⊢ e as τ₂ : τ₂
```

**Index:**

```
    Γ ⊢ e : [τ; _]     Γ ⊢ i : Int
    ────────────────────────────────────  [T-Index-Array]
    Γ ⊢ e[i] : τ

    Γ ⊢ e : (τ₁, …, τₙ)     Γ ⊢ i : Int     0 ≤ i < n
    ──────────────────────────────────────────────────────  [T-Index-Tuple]
    Γ ⊢ e[i] : τᵢ₊₁
```

---

## 4. Unification

### 4.1 Algorithm

Robinson's unification with occurs check and dimensional extension:

```
unify(τ₁, τ₂) : Result<Substitution, TypeError>

unify(α, τ) =
  if α = τ then Ok(∅)
  else if occurs(α, τ) then Err(OccursCheck)
  else Ok({α ↦ τ})

unify(P₁, P₂) where P₁, P₂ primitive =
  if P₁ ≡ P₂ then Ok(∅)
  else Err(Mismatch(P₁, P₂))

unify(τ₁ → τᵣ₁, τ₂ → τᵣ₂) =
  S₁ ← unify(τ₁, τ₂)
  S₂ ← unify(S₁(τᵣ₁), S₁(τᵣ₂))
  Ok(S₂ ∘ S₁)

unify((τ₁₁,…,τ₁ₙ), (τ₂₁,…,τ₂ₘ)) =
  if n ≠ m then Err(Mismatch)
  else fold_unify([(τ₁₁,τ₂₁), …, (τ₁ₙ,τ₂ₙ)])

unify(Resource(P₁,D₁), Resource(P₂,D₂)) =
  S ← unify(P₁, P₂)
  if D₁ = D₂ then Ok(S)
  else Err(DimensionMismatch(D₁, D₂))

unify(Error, _) = Ok(∅)        (error recovery)
unify(_, Error) = Ok(∅)
```

### 4.2 Occurs Check

```
occurs(α, τ) =
  | true    if τ = α
  | true    if τ = N⟨…, τᵢ, …⟩ and occurs(α, τᵢ) for some i
  | true    if τ = τ₁ → τ₂ and (occurs(α, τ₁) or occurs(α, τ₂))
  | true    if τ = (…, τᵢ, …) and occurs(α, τᵢ) for some i
  | true    if τ = [τ'; _] and occurs(α, τ')
  | false   otherwise
```

---

## 5. Generalisation and Instantiation

### 5.1 Generalisation

```
generalize(Γ, τ) = ∀ᾱ. τ
  where ᾱ = ftv(τ) \ ftv(Γ)
  (free type variables in τ not bound in the environment)
```

### 5.2 Instantiation

```
instantiate(∀α₁…αₙ. τ) = τ[α₁ ↦ β₁, …, αₙ ↦ βₙ]
  where β₁, …, βₙ are fresh type variables
```

---

## 6. Trait System

### 6.1 Trait Declaration

```
trait T⟨α₁, …, αₙ⟩ : S₁ + … + Sₘ where P₁, …, Pₖ {
  fn method₁(params) → τ₁;
  type Assoc₁ : Bound₁;
  const CONST₁ : τ_c₁;
}
```

### 6.2 Implementation

```
impl⟨α₁, …, αₙ⟩ T for τ_self where P₁, …, Pₖ {
  fn method₁(self, params) → τ₁ { body }
  type Assoc₁ = τ_concrete;
  const CONST₁ : τ_c₁ = expr;
}
```

### 6.3 Method Resolution

Priority order:
1. Inherent impl methods (registered by type name)
2. Trait impl methods
3. Parent environment

---

## 7. Effect System

### 7.1 Effect Declaration

```
effect E⟨α₁, …, αₙ⟩ {
  op₁(params) → τ₁;
  …
  opₘ(params) → τₘ;
}
```

### 7.2 Handle Expression

```
    Γ ⊢ e : τ     handlers cover all ops of E
    ∀h ∈ handlers: h.resume : τ_resume → τ_final
    ──────────────────────────────────────────────  [T-Handle]
    Γ ⊢ handle e { handlers } : τ_final
```

Note: Effect tracking is declared but not fully enforced in the current
implementation. The type checker parses effect declarations and handle
expressions but does not propagate effect constraints through the type.

---

## 8. Resource Constraints

### 8.1 Constraint Declarations

```
    @requires energy < 100J, latency < 50ms
    ──────────────────────────────────────────────────  [Constraint]
    Injects: energy : Resource(Float, Energy), latency : Resource(Float, Time)
    into function scope
```

### 8.2 Constraint Validation

Constraints are checked declaratively — not solved. The type system ensures
dimensional consistency of constraint expressions but delegates runtime
enforcement to the adaptive function selector.

---

## 9. Error Recovery

The type checker uses `Ty::Error` as a sink type for error recovery:

```
    unify(Error, τ) = Ok(∅)     for any τ
    unify(τ, Error) = Ok(∅)     for any τ
```

This allows multiple type errors to be reported in a single pass rather than
stopping at the first error.

### 9.1 Error Suggestions

The type checker uses Levenshtein distance to suggest alternatives for
undefined variables. The threshold is `max(name.len() / 3, 3)`.

---

## 10. Properties

1. **Soundness** (Type Safety): If `Γ ⊢ e : τ` and `e ⇓ v`, then `v : τ`.
   Currently validated by tests; formal proof in `formal/coq/src/Typing.v`
   (Progress and Preservation theorems).

2. **Principal types:** Algorithm W computes the most general type for every
   well-typed expression.

3. **Decidability:** Type inference is decidable (polynomial in practice,
   theoretical exponential worst case for HM).

4. **Dimensional consistency:** Addition requires matching dimensions;
   multiplication/division follow the group law.

5. **Let-polymorphism:** Definitions bound by `let` are generalised; lambda
   parameters are not.

6. **No implicit narrowing:** Int widened to Float, never Float narrowed to Int.
