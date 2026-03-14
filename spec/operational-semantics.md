# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Eclexia Operational Semantics

**Version:** 1.0.0
**Date:** 2026-03-14
**Extracted from:** `eclexia-interp/src/{eval,value,env,error,builtins}.rs`

---

## 1. Notation

We use standard small-step and big-step operational semantics notation:

- `ρ` — Environment (variable bindings)
- `Σ` — Interpreter state (resource tracking, call depth, method table)
- `ρ, Σ ⊢ e ⇓ v` — Big-step: expression `e` evaluates to value `v`
- `ρ, Σ ⊢ s ⇒ ρ', Σ'` — Statement `s` produces updated environment and state
- `v` — Runtime value
- `⊥` — Error / divergence

---

## 2. Values

```
v ∈ Value ::=
    ()                                          unit
  | b ∈ {true, false}                           boolean
  | n ∈ ℤ₆₄                                    64-bit signed integer
  | f ∈ F₆₄                                    64-bit IEEE 754 float
  | s ∈ String                                 UTF-8 string
  | c ∈ Char                                   Unicode scalar value
  | Resource(f, dim, unit)                      dimensioned quantity
  | (v₁, …, vₙ)                                tuple
  | [v₁, …, vₙ]                                mutable array
  | HashMap{k₁ ↦ v₁, …}                        hash map (string keys)
  | SortedMap{k₁ ↦ v₁, …}                      ordered map
  | Struct(name, {f₁ ↦ v₁, …})                 struct instance
  | Fn(name, params, body, ρ_closure)           function closure
  | AdaptiveFn(name, params, solutions, ρ)      adaptive function
  | Builtin(name, impl)                         built-in function
  | Some(v) | None                              option
  | Sender(tx) | Receiver(rx)                   channel endpoints
  | TaskHandle(h)                               async task handle
  | Macro(rules)                                macro definition
```

### 2.1 Truthiness

Eclexia uses a broad truthiness model:

```
truthy(v) =
  | false       if v ∈ {(), false, None, 0, 0.0, "", []}
  | true        otherwise
```

---

## 3. State

### 3.1 Environment

```
ρ ∈ Env = Ident ⇀ Value

Operations:
  ρ₀                       empty environment
  child(ρ)                  new scope with parent ρ
  ρ(x)                     lookup x (traverses parent chain)
  ρ[x ↦ v]                 define x in current scope
  assign(ρ, x, v)          update x in the scope where it is defined
```

### 3.2 Interpreter State

```
Σ = ⟨ energy_used    : ℝ≥0,
      carbon_used    : ℝ≥0,
      energy_budget  : ℝ>0     (default 1000),
      carbon_budget  : ℝ>0     (default 100),
      shadow_energy  : ℝ>0,
      shadow_carbon  : ℝ>0,
      shadow_latency : ℝ>0,
      call_depth     : ℕ       (max 1000),
      method_table   : TypeName × MethodName ⇀ Fn ⟩
```

### 3.3 Constants

```
MAX_CALL_DEPTH       = 1000
MAX_LOOP_ITERATIONS  = 10,000,000
```

---

## 4. Big-Step Semantics: Expressions

### 4.1 Literals

```
                                    ─────────────────────  [Lit-Int]
                                    ρ, Σ ⊢ n ⇓ n

                                    ─────────────────────  [Lit-Float]
                                    ρ, Σ ⊢ f ⇓ f

                                    ─────────────────────  [Lit-String]
                                    ρ, Σ ⊢ s ⇓ s

                                    ─────────────────────  [Lit-Bool]
                                    ρ, Σ ⊢ b ⇓ b

                                    ─────────────────────  [Lit-Unit]
                                    ρ, Σ ⊢ () ⇓ ()

                                    ───────────────────────────────────  [Lit-Resource]
                                    ρ, Σ ⊢ 100J ⇓ Resource(100.0, Energy, "J")
```

### 4.2 Variables

```
    x ∈ dom(ρ)
    ──────────────────  [Var-Found]
    ρ, Σ ⊢ x ⇓ ρ(x)

    x ∉ dom(ρ)
    ──────────────────────────────────────────  [Var-Undef]
    ρ, Σ ⊢ x ⇓ ⊥("undefined variable: " ++ x)
```

### 4.3 Arithmetic (Binary)

```
    ρ, Σ ⊢ e₁ ⇓ n₁     ρ, Σ ⊢ e₂ ⇓ n₂     n₁, n₂ ∈ ℤ
    ─────────────────────────────────────────────────────  [Add-Int]
    ρ, Σ ⊢ e₁ + e₂ ⇓ n₁ + n₂

    ρ, Σ ⊢ e₁ ⇓ f₁     ρ, Σ ⊢ e₂ ⇓ f₂     f₁, f₂ ∈ F₆₄
    ──────────────────────────────────────────────────────  [Add-Float]
    ρ, Σ ⊢ e₁ + e₂ ⇓ f₁ + f₂

    ρ, Σ ⊢ e₁ ⇓ s₁     ρ, Σ ⊢ e₂ ⇓ s₂     s₁, s₂ ∈ String
    ──────────────────────────────────────────────────────────  [Add-String]
    ρ, Σ ⊢ e₁ + e₂ ⇓ s₁ ++ s₂

    ρ, Σ ⊢ e₁ ⇓ n     ρ, Σ ⊢ e₂ ⇓ f     n ∈ ℤ, f ∈ F₆₄
    ──────────────────────────────────────────────────────  [Add-Mixed]
    ρ, Σ ⊢ e₁ + e₂ ⇓ toFloat(n) + f
```

Subtraction, multiplication follow the same numeric coercion rules.

```
    ρ, Σ ⊢ e₁ ⇓ v₁     ρ, Σ ⊢ e₂ ⇓ v₂     v₂ = 0 ∨ v₂ = 0.0
    ──────────────────────────────────────────────────────────────  [Div-Zero]
    ρ, Σ ⊢ e₁ / e₂ ⇓ ⊥("division by zero")

    ρ, Σ ⊢ e₁ ⇓ v₁     ρ, Σ ⊢ e₂ ⇓ v₂     v₁, v₂ numeric, v₂ ≠ 0
    ─────────────────────────────────────────────────────────────────  [Div]
    ρ, Σ ⊢ e₁ / e₂ ⇓ v₁ / v₂

    ρ, Σ ⊢ e₁ ⇓ n₁     ρ, Σ ⊢ e₂ ⇓ n₂     n₁, n₂ ∈ ℤ, n₂ ≥ 0
    ──────────────────────────────────────────────────────────────  [Pow-Int]
    ρ, Σ ⊢ e₁ ** e₂ ⇓ n₁^n₂                     (right-associative)
```

### 4.4 Comparison and Equality

```
    ρ, Σ ⊢ e₁ ⇓ v₁     ρ, Σ ⊢ e₂ ⇓ v₂
    ──────────────────────────────────────  [Eq]
    ρ, Σ ⊢ e₁ == e₂ ⇓ (v₁ = v₂)

    ρ, Σ ⊢ e₁ ⇓ v₁     ρ, Σ ⊢ e₂ ⇓ v₂     v₁, v₂ numeric
    ──────────────────────────────────────────────────────────  [Lt]
    ρ, Σ ⊢ e₁ < e₂ ⇓ (v₁ < v₂)
```

### 4.5 Logical (Short-Circuit)

```
    ρ, Σ ⊢ e₁ ⇓ v₁     truthy(v₁) = false
    ─────────────────────────────────────────  [And-Short]
    ρ, Σ ⊢ e₁ && e₂ ⇓ false

    ρ, Σ ⊢ e₁ ⇓ v₁     truthy(v₁) = true     ρ, Σ ⊢ e₂ ⇓ v₂
    ──────────────────────────────────────────────────────────────  [And-Eval]
    ρ, Σ ⊢ e₁ && e₂ ⇓ truthy(v₂)

    ρ, Σ ⊢ e₁ ⇓ v₁     truthy(v₁) = true
    ──────────────────────────────────────────  [Or-Short]
    ρ, Σ ⊢ e₁ || e₂ ⇓ true

    ρ, Σ ⊢ e₁ ⇓ v₁     truthy(v₁) = false    ρ, Σ ⊢ e₂ ⇓ v₂
    ──────────────────────────────────────────────────────────────  [Or-Eval]
    ρ, Σ ⊢ e₁ || e₂ ⇓ truthy(v₂)
```

### 4.6 Unary

```
    ρ, Σ ⊢ e ⇓ v     v numeric
    ───────────────────────────  [Neg]
    ρ, Σ ⊢ -e ⇓ -v

    ρ, Σ ⊢ e ⇓ v
    ────────────────────────────  [Not]
    ρ, Σ ⊢ !e ⇓ ¬truthy(v)

    ρ, Σ ⊢ e ⇓ n     n ∈ ℤ
    ────────────────────────────  [BitNot]
    ρ, Σ ⊢ ~e ⇓ ¬n (bitwise)
```

### 4.7 Collections

```
    ∀i. ρ, Σ ⊢ eᵢ ⇓ vᵢ
    ──────────────────────────────────  [Tuple]
    ρ, Σ ⊢ (e₁, …, eₙ) ⇓ (v₁, …, vₙ)

    ∀i. ρ, Σ ⊢ eᵢ ⇓ vᵢ
    ──────────────────────────────────  [Array]
    ρ, Σ ⊢ [e₁, …, eₙ] ⇓ [v₁, …, vₙ]

    ρ, Σ ⊢ e ⇓ v     ρ, Σ ⊢ n ⇓ k     k ∈ ℤ
    ──────────────────────────────────────────  [Array-Repeat]
    ρ, Σ ⊢ [e; n] ⇓ [v, v, …, v]  (k copies)

    ρ, Σ ⊢ e ⇓ [v₀, …, vₙ₋₁]     ρ, Σ ⊢ i ⇓ k     0 ≤ k < n
    ───────────────────────────────────────────────────────────────  [Index]
    ρ, Σ ⊢ e[i] ⇓ vₖ

    ρ, Σ ⊢ e ⇓ [v₀, …, vₙ₋₁]     ρ, Σ ⊢ i ⇓ k     k ≥ n
    ───────────────────────────────────────────────────────────  [Index-OOB]
    ρ, Σ ⊢ e[i] ⇓ ⊥("index out of bounds")
```

### 4.8 Struct Construction and Field Access

```
    ∀i. ρ, Σ ⊢ eᵢ ⇓ vᵢ
    ─────────────────────────────────────────────────────────  [Struct]
    ρ, Σ ⊢ S { f₁: e₁, …, fₙ: eₙ } ⇓ Struct(S, {f₁ ↦ v₁, …, fₙ ↦ vₙ})

    ρ, Σ ⊢ e ⇓ Struct(_, F)     f ∈ dom(F)
    ────────────────────────────────────────  [Field]
    ρ, Σ ⊢ e.f ⇓ F(f)

    ρ, Σ ⊢ e ⇓ Struct(S, F)     f ∉ dom(F)
    ─────────────────────────────────────────────  [Field-Missing]
    ρ, Σ ⊢ e.f ⇓ ⊥("no field '" ++ f ++ "' on " ++ S)
```

### 4.9 Range

```
    ρ, Σ ⊢ e₁ ⇓ a     ρ, Σ ⊢ e₂ ⇓ b     a, b ∈ ℤ
    ──────────────────────────────────────────────────  [Range-Excl]
    ρ, Σ ⊢ e₁..e₂ ⇓ [a, a+1, …, b-1]

    ρ, Σ ⊢ e₁ ⇓ a     ρ, Σ ⊢ e₂ ⇓ b     a, b ∈ ℤ
    ──────────────────────────────────────────────────  [Range-Incl]
    ρ, Σ ⊢ e₁..=e₂ ⇓ [a, a+1, …, b]
```

### 4.10 Type Cast

```
    ρ, Σ ⊢ e ⇓ v
    ──────────────────────────────  [Cast]
    ρ, Σ ⊢ e as T ⇓ cast(v, T)

    where cast(v, T) =
      | Int:    v if Int, ⌊v⌋ if Float, 0/1 if Bool, ord(v) if Char, parse if String
      | Float:  v if Float, toFloat if Int, 0.0/1.0 if Bool, parse if String
      | String: format(v) for any v
      | Bool:   truthy(v)
      | Char:   chr(v) if Int
      | ⊥       otherwise
```

### 4.11 Try Operator

```
    ρ, Σ ⊢ e ⇓ Some(v)
    ─────────────────────  [Try-Some]
    ρ, Σ ⊢ e? ⇓ v

    ρ, Σ ⊢ e ⇓ None
    ──────────────────────────────────────  [Try-None]
    ρ, Σ ⊢ e? ⇓ ⊥("try (?) on None value")

    ρ, Σ ⊢ e ⇓ Struct("Ok", {_0 ↦ v})
    ────────────────────────────────────  [Try-Ok]
    ρ, Σ ⊢ e? ⇓ v

    ρ, Σ ⊢ e ⇓ Struct("Err", {_0 ↦ err})
    ────────────────────────────────────────────────────  [Try-Err]
    ρ, Σ ⊢ e? ⇓ ⊥("try on Err: " ++ format(err))
```

---

## 5. Big-Step Semantics: Statements

### 5.1 Let Binding

```
    ρ, Σ ⊢ e ⇓ v     binds = match(pat, v)
    ──────────────────────────────────────────  [Let]
    ρ, Σ ⊢ let pat = e ⇒ ρ ∪ binds, Σ
```

### 5.2 Assignment

```
    ρ, Σ ⊢ e ⇓ v     x ∈ dom(ρ)
    ──────────────────────────────────────  [Assign]
    ρ, Σ ⊢ x = e ⇒ ρ[x ↦ v], Σ

    ρ, Σ ⊢ e₁ ⇓ Struct(S, F)     ρ, Σ ⊢ e₂ ⇓ v
    ───────────────────────────────────────────────  [Assign-Field]
    ρ, Σ ⊢ e₁.f = e₂ ⇒ ρ[e₁ ↦ Struct(S, F[f ↦ v])], Σ

    ρ, Σ ⊢ arr ⇓ [v₀, …, vₙ₋₁]     ρ, Σ ⊢ i ⇓ k     ρ, Σ ⊢ e ⇓ v
    ──────────────────────────────────────────────────────────────────  [Assign-Index]
    ρ, Σ ⊢ arr[i] = e ⇒ ρ (arr mutated in place: arr[k] ← v), Σ
```

### 5.3 Return, Break, Continue

These are modelled as exceptional control flow:

```
    ρ, Σ ⊢ e ⇓ v
    ─────────────────────────────────  [Return]
    ρ, Σ ⊢ return e ⇒ raise Return(v)

    ──────────────────────────────────  [Break]
    ρ, Σ ⊢ break ⇒ raise Break

    ──────────────────────────────────  [Continue]
    ρ, Σ ⊢ continue ⇒ raise Continue
```

### 5.4 If Statement

```
    ρ, Σ ⊢ cond ⇓ v     truthy(v) = true     ρ, Σ ⊢ then ⇒ ρ', Σ'
    ───────────────────────────────────────────────────────────────────  [If-True]
    ρ, Σ ⊢ if cond { then } else { els } ⇒ ρ', Σ'

    ρ, Σ ⊢ cond ⇓ v     truthy(v) = false     ρ, Σ ⊢ els ⇒ ρ', Σ'
    ────────────────────────────────────────────────────────────────────  [If-False]
    ρ, Σ ⊢ if cond { then } else { els } ⇒ ρ', Σ'

    ρ, Σ ⊢ cond ⇓ v     truthy(v) = false     no else branch
    ────────────────────────────────────────────────────────────  [If-NoElse]
    ρ, Σ ⊢ if cond { then } ⇒ ρ, Σ
```

### 5.5 While Loop

```
    ρ, Σ ⊢ cond ⇓ v     truthy(v) = false
    ──────────────────────────────────────────  [While-Done]
    ρ, Σ ⊢ while cond { body } ⇒ ρ, Σ

    ρ, Σ ⊢ cond ⇓ v     truthy(v) = true
    ρ, Σ ⊢ body ⇒ ρ₁, Σ₁     (or catch Continue)
    Σ₁.iterations < MAX_LOOP_ITERATIONS
    ρ₁, Σ₁ ⊢ while cond { body } ⇒ ρ', Σ'
    ──────────────────────────────────────────────  [While-Step]
    ρ, Σ ⊢ while cond { body } ⇒ ρ', Σ'

    Σ.iterations ≥ MAX_LOOP_ITERATIONS
    ────────────────────────────────────────────────  [While-Limit]
    ρ, Σ ⊢ while cond { body } ⇒ ⊥("max loop iterations")
```

Break is caught by the loop and terminates it.

### 5.6 For Loop

```
    ρ, Σ ⊢ iter ⇓ [v₁, …, vₙ]
    ∀i ∈ 1..n:
      ρᵢ = child(ρ) ∪ match(pat, vᵢ)
      ρᵢ, Σᵢ ⊢ body ⇒ _, Σᵢ₊₁     (catch Break → terminate; catch Continue → next)
    ──────────────────────────────────────────────────────────────────  [For]
    ρ, Σ ⊢ for pat in iter { body } ⇒ ρ, Σₙ₊₁
```

### 5.7 Match Expression

```
    ρ, Σ ⊢ scrutinee ⇓ v
    ∃i: match(armᵢ.pat, v) = binds ∧
        (armᵢ.guard absent ∨ ρ ∪ binds, Σ ⊢ armᵢ.guard ⇓ truthy)
    ρ ∪ binds, Σ ⊢ armᵢ.body ⇓ v'
    ────────────────────────────────────────────────────────────────  [Match]
    ρ, Σ ⊢ match scrutinee { arm₁, …, armₙ } ⇓ v'

    ∀i: match(armᵢ.pat, v) = ∅ ∨ guard fails
    ────────────────────────────────────────────────  [Match-Fail]
    ρ, Σ ⊢ match scrutinee { … } ⇓ ⊥("no matching pattern")
```

---

## 6. Pattern Matching

```
match : Pattern × Value → Option<Bindings>

match(_, v)                        = {}                         [Pat-Wild]
match(x, v)                        = {x ↦ v}                   [Pat-Var]
match(lit, v)                      = {} if eval(lit) = v        [Pat-Lit]
match((p₁,…,pₙ), (v₁,…,vₙ))      = ⋃ᵢ match(pᵢ, vᵢ)         [Pat-Tuple]
match(C(p₁,…,pₙ), Struct(C, F))   = ⋃ᵢ match(pᵢ, F[i])       [Pat-Ctor]
match(p₁ | p₂, v)                  = first success              [Pat-Or]
match(a..b, v)                     = {} if a ≤ v < b            [Pat-Range]
match(a..=b, v)                    = {} if a ≤ v ≤ b            [Pat-RangeIncl]
match(x @ p, v)                    = match(p, v) ∪ {x ↦ v}     [Pat-Binding]
match({f₁: p₁, …}, Struct(_, F))  = ⋃ᵢ match(pᵢ, F(fᵢ))      [Pat-Struct]
match([p₁,…,pₙ], [v₁,…,vₙ])      = ⋃ᵢ match(pᵢ, vᵢ)         [Pat-Slice]
match(&p, v)                       = match(p, v)                [Pat-Ref]
match(.., _)                       = {}                         [Pat-Rest]
```

---

## 7. Function Calls

### 7.1 User-Defined Functions

```
    ρ, Σ ⊢ e₀ ⇓ Fn(name, [p₁,…,pₙ], body, ρ_clos)
    ∀i. ρ, Σ ⊢ aᵢ ⇓ vᵢ
    n = len([a₁,…,aₘ])     m = n
    Σ.call_depth < MAX_CALL_DEPTH
    ρ_call = child(ρ_clos)[p₁ ↦ v₁, …, pₙ ↦ vₙ]
    ρ_call, Σ[call_depth + 1] ⊢ body ⇓ v'     (catch Return(v') → v')
    ────────────────────────────────────────────────────────────────  [Call]
    ρ, Σ ⊢ e₀(a₁, …, aₘ) ⇓ v'

    m ≠ n
    ───────────────────────────────────────────────  [Call-Arity]
    ρ, Σ ⊢ e₀(a₁, …, aₘ) ⇓ ⊥("arity mismatch")

    Σ.call_depth ≥ MAX_CALL_DEPTH
    ──────────────────────────────────────────────  [Call-Overflow]
    ρ, Σ ⊢ e₀(…) ⇓ ⊥("max call depth exceeded")
```

### 7.2 Method Calls

```
    ρ, Σ ⊢ receiver ⇓ v     type_name(v) = T
    Σ.method_table(T, m) = Fn(…) ∨ ρ(T::m) = Fn(…)
    ρ, Σ ⊢ Fn(…)(v, a₁, …, aₙ) ⇓ v'
    ─────────────────────────────────────────────────  [Method]
    ρ, Σ ⊢ receiver.m(a₁, …, aₙ) ⇓ v'
```

### 7.3 Lambda / Closure

```
    ─────────────────────────────────────────────────────────  [Lambda]
    ρ, Σ ⊢ |p₁, …, pₙ| e ⇓ Fn("<lambda>", [p₁,…,pₙ], e, ρ)
```

---

## 8. Adaptive Functions

### 8.1 Solution Selection with Guards

```
    ρ, Σ ⊢ e₀ ⇓ AdaptiveFn(name, params, [sol₁,…,solₖ], ρ_clos)
    ∀i. ρ, Σ ⊢ aᵢ ⇓ vᵢ
    ρ_call = child(ρ_clos)[params ↦ args]

    feasible = { solⱼ | solⱼ.requires ≤ Σ.budgets }
    guarded  = { solⱼ ∈ feasible | solⱼ.when absent ∨ ρ_call, Σ ⊢ solⱼ.when ⇓ true }

    best = argmin_{solⱼ ∈ guarded}(
      Σ.shadow_energy × solⱼ.energy_cost
      + Σ.shadow_latency × solⱼ.latency_cost
      + Σ.shadow_carbon × solⱼ.carbon_cost
    )

    ρ_call, Σ' ⊢ best.body ⇓ v'
    Σ'' = Σ'[energy_used += best.energy, carbon_used += best.carbon]
    ────────────────────────────────────────────────────────────  [Adaptive-Select]
    ρ, Σ ⊢ e₀(a₁, …, aₙ) ⇓ v'

    feasible = ∅
    ──────────────────────────────────────────────────────────  [Adaptive-NoSolution]
    ρ, Σ ⊢ e₀(…) ⇓ ⊥("no suitable solution for " ++ name)
```

### 8.2 Resource Budget Enforcement

```
    Σ.energy_used + cost > Σ.energy_budget
    ──────────────────────────────────────────────────────────  [Resource-Exceeded]
    ρ, Σ ⊢ call ⇓ ⊥("calling '" ++ name ++ "' would exceed energy budget")
```

---

## 9. Block Evaluation

```
    ρ_block = child(ρ)
    ρ_block, Σ ⊢ s₁ ⇒ ρ₁, Σ₁     …     ρₙ₋₁, Σₙ₋₁ ⊢ sₙ ⇒ ρₙ, Σₙ
    ρₙ, Σₙ ⊢ e_tail ⇓ v     (if present; otherwise v = ())
    ────────────────────────────────────────────────────────────────  [Block]
    ρ, Σ ⊢ { s₁; …; sₙ; e_tail } ⇓ v
```

Bindings in ρ_block do not escape to ρ.

---

## 10. Program Execution

```
    ρ₀ = ∅     register_builtins(ρ₀)
    ∀item ∈ file.items: register(item, ρ₀, Σ₀)
    ρ₀("main") = Fn(…) ⟹ ρ₀, Σ₀ ⊢ main() ⇓ v
    ρ₀("main") = ⊥     ⟹ v = ()
    ────────────────────────────────────────────  [Program]
    run(file) ⇓ v
```

---

## 11. Error Semantics

Errors propagate upward through the evaluation, unwinding the stack until caught
by a handler (match, try operator) or reaching the top level.

Control flow signals (Return, Break, Continue) are not true errors — they are
caught by their enclosing construct (function body, loop).

```
Error ::=
  | UndefinedVariable(name)
  | TypeError(expected, got)
  | ArityMismatch(expected, got)
  | DivisionByZero
  | IndexOutOfBounds(index, length)
  | NoSuchField(struct_name, field_name)
  | NotCallable(type_name)
  | ResourceViolation(message)
  | NoSuitableSolution(function_name)
  | MaxCallDepthExceeded
  | MaxLoopIterationsExceeded
  | Custom(message)

ControlFlow ::=
  | Return(value)
  | Break(option<value>)
  | Continue
```

---

## 12. Invariants

1. **Lexical scoping:** Blocks create child environments; bindings do not leak.
2. **Call depth bounded:** Recursion limited to 1000 frames.
3. **Loop iterations bounded:** While/for limited to 10M iterations.
4. **Resource monotonicity:** `energy_used` and `carbon_used` are monotonically
   non-decreasing throughout execution.
5. **Shadow price monotonicity:** Shadow prices increase with resource scarcity
   (proved in `formal/coq/src/ShadowPrices.v`).
6. **Adaptive optimality:** The selected solution minimises weighted resource
   cost among feasible alternatives.
7. **Short-circuit evaluation:** `&&` and `||` do not evaluate the right operand
   when the left operand determines the result.
8. **Implicit numeric coercion:** Int is widened to Float in mixed arithmetic;
   no implicit narrowing.
