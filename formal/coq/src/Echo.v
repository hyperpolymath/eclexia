(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)
(* Echo types: structured loss as fibres, with the total-space equivalence. *)

(** * Echo types — semantic justification for Eclexia's [Echo[A, B]]

    This module mechanises the load-bearing core of the echo-types
    development (hyperpolymath/echo-types) that justifies Eclexia's
    [Echo[A, B]] type former and its [echo] / [echo_witness] / [echo_base]
    intrinsics (see compiler/eclexia-typeck and compiler/eclexia-interp).

    An echo of a map [f : A -> B] at a base [y] is a fibre element: a
    retained witness [x : A] together with a proof that [f x = y]. The
    runtime mirrors this exactly — an echo value pairs the witness with the
    observed base [f x]. We prove the two properties that make echoes a
    notion of *structured loss*:

      - structured loss: when [f] collapses distinct inputs to one output,
        their echoes agree on the observed base but keep distinct
        witnesses (the distinction [f] erased is recovered);

      - total-space equivalence [A ≃ Σ (y : B), Echo f y]: recording every
        echo makes an irreversible [f] reversible. This is the echo-types
        "irreversible computation + echo = reversible representation"
        keystone (EchoTotalCompletion).

    Everything is constructive and axiom-free; it builds under coqc 8.18. *)

Section Echo.

  Context {A B : Type}.
  Variable f : A -> B.

  (** An echo of [f] at [y] is the fibre of [f] over [y]. *)
  Definition Echo (y : B) : Type := { x : A & f x = y }.

  (** Introduction: every input sits in its own fibre, at base [f x]. *)
  Definition echo_intro (x : A) : Echo (f x) := existT _ x eq_refl.

  (** The retained witness (first projection of the fibre). *)
  Definition echo_witness {y : B} (e : Echo y) : A := projT1 e.

  (** The observed base of an echo (the fibre index). *)
  Definition echo_base {y : B} (_ : Echo y) : B := y.

  (** ** Computation / coherence rules (these mirror the interpreter). *)

  (** The witness of an introduced echo is exactly the input. *)
  Lemma echo_witness_intro : forall x : A, echo_witness (echo_intro x) = x.
  Proof. intro x. reflexivity. Qed.

  (** The base of an introduced echo is exactly [f x]. *)
  Lemma echo_base_intro : forall x : A, echo_base (echo_intro x) = f x.
  Proof. intro x. reflexivity. Qed.

  (** Fibre coherence: applying [f] to the retained witness always recovers
      the observed base. This is the invariant the runtime maintains by
      construction (it stores [base = f witness]). *)
  Lemma echo_base_witness :
    forall (y : B) (e : Echo y), f (echo_witness e) = echo_base e.
  Proof. intros y [x p]. exact p. Qed.

  (** ** Structured loss

      If [f] collapses two distinct inputs to the same output, their echoes
      agree on the observed base yet disagree on the retained witness:
      loss that is not erasure. *)
  Theorem echo_structured_loss :
    forall x1 x2 : A,
      f x1 = f x2 ->     (* the map collapses them to one base ... *)
      x1 <> x2 ->        (* ... though they are distinct ... *)
      echo_base (echo_intro x1) = echo_base (echo_intro x2)        (* bases agree *)
      /\ echo_witness (echo_intro x1) <> echo_witness (echo_intro x2). (* witnesses differ *)
  Proof.
    intros x1 x2 Hbase Hneq. split.
    - simpl. exact Hbase.
    - simpl. exact Hneq.
  Qed.

  (** ** Total-space equivalence : A ≃ Σ (y : B), Echo f y

      Bundling each echo with its base reconstructs the entire domain, so an
      irreversible [f] becomes reversible once its echoes are recorded. *)

  Definition echo_total_to (x : A) : { y : B & Echo y } :=
    existT _ (f x) (echo_intro x).

  Definition echo_total_from (p : { y : B & Echo y }) : A :=
    echo_witness (projT2 p).

  (** One round-trip is definitional. *)
  Theorem echo_total_from_to :
    forall x : A, echo_total_from (echo_total_to x) = x.
  Proof. intro x. reflexivity. Qed.

  (** The other holds by eliminating the fibre's equality proof. *)
  Theorem echo_total_to_from :
    forall p : { y : B & Echo y }, echo_total_to (echo_total_from p) = p.
  Proof.
    intros [y [x p]]. simpl.
    destruct p. reflexivity.
  Qed.

End Echo.
