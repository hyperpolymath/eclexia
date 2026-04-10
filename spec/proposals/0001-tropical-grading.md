# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Proposal 0001: Tropical Grading for Eclexia

**Status:** DRAFT
**Author:** Jonathan D.A. Jewell
**Created:** 2026-04-10
**Type:** Type system extension
**Scope:** `compiler/eclexia-ast`, `compiler/eclexia-typeck`, `compiler/eclexia-effects`, `compiler/eclexia-absinterp`, `compiler/eclexia-parser`, `spec/type-system.md`, `formal/`
**Depends on:** existing QTT grading (FORMAL_VERIFICATION.md §11), shadow-price engine, `ResourceConstraint`, `eclexia-effects` row polymorphism
**Blocks:** nothing operational; this is a spec-first design proposal

---

## Summary

Generalise Eclexia's existing graded modality (`□[r] A`, currently hard-wired to the ℕ-semiring for usage counting) over an arbitrary **ordered commutative semiring**, and supply two canonical non-arithmetic instances — **max-plus** and **min-plus** — so the type system can reason about worst-case latency, shortest-path cost, and critical-path scheduling *as type-level theorems* rather than as ad-hoc resource-constraint inequalities.

This is not a new type constructor. It is a generalisation of machinery that already exists.

## Motivation

### The gap Eclexia has today

Eclexia already has *three* partially-overlapping mechanisms for reasoning about cost-like quantities at the type level:

1. **QTT grading** (`□[r] A` with `r ∈ ℕ`, per FORMAL_VERIFICATION.md §11.1) — counts usage. Provably sound against the ℕ-semiring. Cannot express "worst-case latency 3.2 ms" because `+` on latencies is ℕ-addition, and composing two latency bounds under sequential control flow requires ℕ-addition, while composing two latency bounds under *parallel* control flow requires `max`. QTT uses the wrong algebra for the job.

2. **Resource constraints** (`types.rs:269-279`, `ResourceConstraint { resource, dimension, op, bound }`) — attach latency/energy/carbon bounds to types. The solver (`infer.rs`) composes these with hand-written per-case rules. Every composition law is a one-off lemma. There is no algebra to lean on.

3. **Shadow-price engine with LP duality** (`runtime/shadow_prices.rs`, proven in `formal/ShadowPrices.v` to zero `Admitted` modulo five cited axioms) — the *runtime* cost model. Uses LP duality to compute shadow prices for resources. This is deep tropical geometry in disguise: LP duality over the real semiring is isomorphic to the max-plus semiring under the log/exp transform; the simplex tableau is a tropical polynomial. Eclexia already computes tropical quantities, it just doesn't *type* them.

The three mechanisms are proving the same things three times in three different formalisms. A single graded modality over an abstract semiring unifies all three.

### Why tropical, specifically

In tropical algebra:
- `a ⊕ b := min(a, b)` (or `max`), identity `+∞` (or `−∞`)
- `a ⊗ b := a + b`, identity `0`

These are *exactly* the operations you want for:

- **Sequential composition composes latencies**: if `f : □[τ, t₁] A → B` and `g : □[τ, t₂] B → C` then `g ∘ f : □[τ, t₁ ⊗ t₂] A → C`. Under max-plus, `⊗ = +`, so total latency is additive on sequential paths. Correct.
- **Parallel composition takes the worst case**: if `f ∥ g` with latencies `t₁, t₂` then the join has latency `t₁ ⊕ t₂`. Under max-plus, `⊕ = max`, so parallel composition takes the maximum. Correct.
- **Choice composes optimistically (shortest path)**: under min-plus, `⊕ = min`, so `if e then f else g` has latency `min(t₁, t₂)` in the best-case-bound fragment.

Every one of these is a type-level theorem today in Eclexia only via hand-proved lemmas in the resource-constraint solver. Under a tropical-graded modality they become the *defining rule* for the modality.

## Non-goals

- Not replacing QTT grading. ℕ-grading remains, as the `NatSemiring` instance.
- Not adding a new surface type. Tropical types live inside the existing `□[·, ·] A` modality.
- Not touching the runtime. The runtime shadow-price engine is already tropical under the hood; this proposal aligns the type system with what the runtime already computes.
- Not mandating tropical grading for every function. Opt-in annotation; un-annotated functions default to the ℕ-semiring as today.

## Design

### 1. Semirings as first-class, parameterised over a dimension

```
-- Proposal syntax in Eclexia spec form; not yet legal .ecl source.
semiring NatCounting : OrderedCommutativeSemiring[ℕ] {
    zero  = 0
    one   = 1
    plus  = (+)
    times = (·)
    leq   = (≤)
}

semiring MaxPlus[D : Dimension] : OrderedCommutativeSemiring[ℝ∞] {
    zero  = -∞         -- identity of ⊕ = max
    one   = 0          -- identity of ⊗ = +
    plus  = max
    times = (+)
    leq   = (≤)
    -- NOT cancellative. See soundness §5.
}

semiring MinPlus[D : Dimension] : OrderedCommutativeSemiring[ℝ∞] {
    zero  = +∞
    one   = 0
    plus  = min
    times = (+)
    leq   = (≥)        -- order reversed: smaller = better
}
```

The `[D : Dimension]` parameter ties the semiring carrier to Eclexia's existing `Dimension` algebra (`eclexia-ast/src/dimension.rs`). `MaxPlus[Milliseconds]` and `MaxPlus[Joules]` are distinct types; you cannot compose them without an explicit conversion. This reuses dimensional analysis rather than bolting on a parallel numeric tower.

### 2. Generalised graded modality

Current (implicit) form in FORMAL_VERIFICATION.md §11:
```
Γ ⊢ e : □[r] A        -- r ∈ ℕ, always
```

Proposed form:
```
Γ ⊢ e : □[S, r] A     -- S a semiring instance, r ∈ carrier(S)
```

The old `□[r] A` becomes sugar for `□[NatCounting, r] A`. Every existing program re-typechecks unchanged.

### 3. Typing rules

Let `S : OrderedCommutativeSemiring[T]`. The core grading rules generalise as follows (abbreviating `□[S, r]` as `□r`):

```
(Var)   Γ, x : □_{𝟙_S} A ⊢ x : A

(Abs)   Γ, x : □r A ⊢ e : B
        ─────────────────────
        Γ ⊢ λx. e : □r A → B

(App)   Γ ⊢ f : □r A → B     Δ ⊢ a : A
        ────────────────────────────────
        Γ, r ⊗_S Δ ⊢ f a : B

(Sub)   Γ ⊢ e : □r A     r ≤_S s
        ──────────────────────────
        Γ ⊢ e : □s A

(Seq)   Γ ⊢ e₁ : □r A     Δ ⊢ e₂ : □s B   -- sequenced in control flow
        ───────────────────────────────────
        Γ, Δ ⊢ e₁; e₂ : □_{r ⊗_S s} B

(Par)   Γ ⊢ e₁ : □r A     Δ ⊢ e₂ : □s B   -- composed in parallel
        ───────────────────────────────────
        Γ, Δ ⊢ e₁ ∥ e₂ : □_{r ⊕_S s} (A × B)
```

Read `Par` with `S = MaxPlus[Milliseconds]`: the latency of a parallel join is the `max` of its branches. Read it with `S = NatCounting`: the sum of usages. The same rule, different witnesses.

### 4. Surface syntax

Minimum viable — one new annotation site on the modality:

```eclexia
// Latency-bounded function: 3.2 ms worst case.
fn handle_request(req: Request) -> Response
    graded[MaxPlus[Milliseconds], 3.2] { ... }

// Existing syntax still works, elaborates to graded[NatCounting, 1]:
fn once(x: A) -> B graded[1] { ... }
```

Alternative considered: dedicated `@latency`, `@cost` annotations. Rejected because it fragments the surface into N parallel annotation systems that all desugar to the same graded modality. One system, N semirings.

### 5. Soundness obligations

This is the expensive part. The existing proof development proves type safety for `□[r] A` with `r ∈ ℕ` in `formal/Typing.v`. Generalising requires:

- **O1. Abstract the type-safety theorem** over `S : OrderedCommutativeSemiring`. Progress and preservation go through unchanged where the proof uses `+`/`0`/`≤` generically. Flagged places in the current proof that must be audited:
  - Any lemma using cancellation of ℕ-addition (max-plus is **not cancellative**: `max(3, 5) = max(4, 5) = 5` but `3 ≠ 4`). Every such lemma must either be restricted to cancellative semirings or re-proved without cancellation.
  - Any lemma using well-foundedness of `<` on ℕ for termination of resource-bound computations. `ℝ∞` with `<` is not well-founded; substitute a structural well-founded relation on the syntax tree, which is what modern QTT developments do anyway (Abel et al.).
  - Any lemma using discreteness of ℕ (e.g. `r = s ∨ r < s ∨ r > s` is decidable). For `ℝ∞`, decidability of the grade order becomes a typeclass obligation on `S`.

- **O2. Prove the `NatSemiring` instance** reproduces the existing (already-proved) ℕ-graded system, to validate the abstraction.

- **O3. Prove the `MaxPlus[D]` and `MinPlus[D]` instances** satisfy the ordered-commutative-semiring laws + decidable `≤_S`. Straightforward but must be done.

- **O4. Show that `□[MaxPlus[Milliseconds], t] A` composes under sequential and parallel control in the way `Seq` and `Par` claim**. This is a *use-site* theorem: it proves that the typing rule's grade matches the actual worst-case latency on the reduction. The analogous theorem for ℕ in the current development is "grades count steps", which is O1's thin existing twin.

- **O5. Connect to the shadow-price engine**. The LP duality proof in `ShadowPrices.v` (5 cited `Axiom`s, 0 `Admitted`) should be re-stated as "the shadow prices computed by the runtime are the optimal dual of the tropical polynomial defined by the graded type of the program". If this works, one of the five axioms (LP strong duality) becomes provable in the tropical setting by a direct combinatorial argument over longest-path DAGs, retiring an axiom.

Estimated proof-engineering effort: **2–4 weeks of focused work**, mostly on O1. Most of the existing proof script goes through with `+ ↦ ⊗`, `0 ↦ 𝟘`, `≤ ↦ ≤_S` substitutions. The genuinely new work is O4 and the cancellation-free versions of a handful of lemmas in O1.

### 6. Decidability of constraint solving

Under `NatCounting`, grade inequalities reduce to Presburger arithmetic. Under `MaxPlus[D]` / `MinPlus[D]`, they reduce to **tropical linear arithmetic** — decidable but with different complexity characteristics:

- **Conjunctions of tropical linear inequalities over bounded-degree tropical polynomials**: decidable in polynomial time by reduction to **longest-path / shortest-path in a weighted DAG**. This is the fragment Eclexia actually needs for worst-case latency analysis.
- **General tropical LP**: decidable, polynomial-time via max-plus Bellman–Ford or tropical simplex, though with worse constants than Presburger.
- **Tropical polynomial satisfiability (nonlinear)**: NP-hard in general. Stay out of this fragment.

The solver in `eclexia-typeck/src/infer.rs` must dispatch on the semiring instance. Suggested architecture:

```
// In new eclexia-typeck/src/semiring.rs
trait SemiringSolver {
    fn zero(&self) -> Grade;
    fn one(&self) -> Grade;
    fn plus(&self, a: Grade, b: Grade) -> Grade;
    fn times(&self, a: Grade, b: Grade) -> Grade;
    fn leq(&self, a: Grade, b: Grade) -> bool;
    fn solve_constraints(&self, cs: &[GradeConstraint]) -> SolverResult;
}

struct NatSolver;          // Presburger (existing code extracted)
struct MaxPlusSolver<D>;   // DAG longest-path for linear fragment
struct MinPlusSolver<D>;   // DAG shortest-path for linear fragment
```

The `eclexia-absinterp` abstract-interpretation layer can feed tropical intervals (pairs of min-plus and max-plus bounds) directly into this solver, giving sound-by-construction cost bounds.

### 7. Interaction with existing machinery

- **Dimensional analysis** (`dimension.rs`): tropical grades carry dimensions, so `max(3 ms, 5 J)` is a type error before it reaches the solver. No changes to `dimension.rs` needed; just constrain the semiring carrier.
- **Row-polymorphic effects** (`eclexia-effects/src/row.rs`): effect rows can themselves be graded tropically, giving per-effect latency bounds. Out of scope for v1 of this proposal; noted as follow-up.
- **Shadow prices** (`runtime/shadow_prices.rs`): the runtime's shadow prices are the dual of the tropical polynomial defined by the type. This lets the shadow-price axioms be restated as type-level theorems (see O5). This is the biggest win and the reason this proposal is worth the proof cost.
- **Backends**: nothing changes. Grading is erased at runtime (as it is today for ℕ). The WASM/LLVM/Cranelift backends see the same post-erasure MIR.

## Files to change

| File | Change |
|---|---|
| `compiler/eclexia-ast/src/types.rs` | Parameterise `Grade` and `ResourceConstraint` over a `SemiringId` handle. |
| `compiler/eclexia-typeck/src/infer.rs` | Dispatch grade composition on semiring instance. Keep ℕ fast-path. |
| `compiler/eclexia-typeck/src/semiring.rs` | **NEW.** `SemiringSolver` trait + `NatSolver`, `MaxPlusSolver`, `MinPlusSolver`. |
| `compiler/eclexia-parser/src/` | Accept `graded[<semiring>, <grade>]` syntax. Lex `MaxPlus`, `MinPlus` as semiring identifiers in the type position. |
| `compiler/eclexia-effects/src/row.rs` | Note follow-up work on tropical-graded effects. No code changes in v1. |
| `compiler/eclexia-absinterp/src/resource.rs` | Feed tropical intervals into the new solver when in scope. |
| `spec/type-system.md` | Rewrite §9 grading rules over an abstract semiring. |
| `spec/grammar.ebnf` | Add `graded[<semiring-expr>, <grade-expr>]` production. |
| `formal/Typing.v` | Abstract the type-safety theorem per O1. |
| `formal/TropicalSemiring.v` | **NEW.** Instance + O3/O4 proofs. |
| `formal/ShadowPrices.v` | Rephrase per O5 — possibly retire one axiom. |
| `stdlib/Tropical.ecl` | **NEW.** `Latency`, `Cost`, `Priority` aliases as graded types. |
| `examples/12-tropical-latency.ecl` | **NEW.** Worked example: critical-path scheduling as a type-level theorem. |

## Implementation plan

**Phase 0 — this proposal.** Review, iterate, accept.

**Phase 1 — spec-first (1 week).** Rewrite `spec/type-system.md §9` over abstract semirings. Update `grammar.ebnf`. Add draft examples. No compiler changes yet.

**Phase 2 — proofs (2–4 weeks).** Execute O1 through O4. Land `formal/TropicalSemiring.v`. Keep `Typing.v` passing for the ℕ instance throughout.

**Phase 3 — compiler (1–2 weeks).** Land `semiring.rs`. Extend the parser. Wire the solver. Write the `Tropical.ecl` stdlib module and the example.

**Phase 4 — shadow-price alignment (optional, 1–2 weeks).** Execute O5. Retire the LP strong-duality axiom if the direct tropical proof works.

Total: **5–9 weeks** including proofs. Implementation without the proof work is 1–2 weeks but would land an unsoundness risk that the rest of Eclexia is careful to avoid.

## Open questions

1. **Grade polymorphism.** Should users be able to write `∀S : OrderedCommutativeSemiring. □[S, r] A`? Useful for generic libraries; adds a new quantifier. Proposed answer: **no for v1**, revisit after tropical lands.
2. **Graded effect rows.** Can effect rows be graded tropically? Almost certainly yes; punt to a follow-up proposal after v1 validates the single-grade case.
3. **Relationship to PanLL constraint core.** PanLL's Phase 3 constraint core (per `memory/panll-phase3-constraint-core.md`) is doing similar work from the constraint side. Coordination needed before Phase 1 lands so the two constraint languages don't diverge.
4. **Does this subsume the resource-constraint solver?** In principle yes — `ResourceConstraint { resource, dim, op, bound }` is a tropical inequality in disguise. In practice the migration is a big refactor that should come *after* the tropical solver is proven correct in isolation.

## Rejected alternatives

- **Add a new `Ty::Tropical` constructor.** Rejected: bifurcates the type system, doesn't compose with existing QTT machinery, duplicates every rule. The graded modality is already the right place.
- **Encode latencies as phantom types on refinement types.** Rejected: no compositional algebra; every composition is a hand-written SMT query. This is what the current `ResourceConstraint` solver effectively does, and the fact that it needs per-case lemmas is exactly the pain this proposal removes.
- **Add a new `@latency` annotation system parallel to grading.** Rejected: two parallel cost systems is worse than one. Unify under the graded modality.

## References

- Abel, A. et al., *Quantitative Type Theory*, TYPES 2018 — QTT formulation this proposal generalises.
- Atkey, R., *Syntax and Semantics of Quantitative Type Theory*, LICS 2018 — semiring-generic QTT.
- Butković, P., *Max-linear Systems: Theory and Algorithms*, Springer 2010 — tropical linear algebra and decidability.
- Maclagan, D. & Sturmfels, B., *Introduction to Tropical Geometry*, AMS 2015 — LP-tropical duality (relevant to O5).
- Eclexia internal: `FORMAL_VERIFICATION.md §11`, `formal/Typing.v`, `formal/ShadowPrices.v`, `eclexia-ast/src/types.rs:269-279`, `eclexia-typeck/src/infer.rs`, `eclexia-absinterp/src/resource.rs`.
