(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)
(* Landauer / Bennett: the thermodynamic price of erasing an echo's witness. *)

Require Import Coq.Arith.PeanoNat.

(** * Thermodynamic cost of structured loss

    Bridges Echo (formal/coq/src/Echo.v) to Eclexia's energy resource.

    Collapsing a fibre of [n] distinguishable witnesses down to its single
    observed base erases [log2 n] bits of information. By Landauer's
    principle that costs at least [k * T * ln 2] of energy per bit — exactly
    the [Resource[Energy]] that Eclexia prices via the [landauer_cost]
    intrinsic (compiler/eclexia-typeck, compiler/eclexia-interp). Retaining
    the echo's witness keeps the computation reversible (Bennett): nothing is
    erased, so the cost is zero. Information loss thereby enters the resource
    economy — the graded-comonad-of-loss reading of THEORY.md S5.5.

    This module proves the discrete (bit-count) shadow of that story,
    axiom-free; the real-valued [k T ln 2] scaling lives in the runtime
    intrinsic. It mirrors echo-types' EchoThermodynamics (bennett-reversible,
    landauer-collapse). *)

(** Bits erased when a fibre of [fibre_size] witnesses is collapsed to its
    single base. (The fibre size is the number of distinct witnesses an echo
    map sends to one observed output — see Echo.v.) *)
Definition erasure_bits (fibre_size : nat) : nat := Nat.log2 fibre_size.

(** A collapse is *reversible* exactly when at most one witness reaches the
    base: there is nothing to erase, and the input is recoverable. *)
Definition reversible (fibre_size : nat) : Prop := fibre_size <= 1.

(** ** Bennett: a reversible collapse erases no information, so it is free. *)
Theorem bennett_reversible_is_free :
  forall n : nat, reversible n -> erasure_bits n = 0.
Proof.
  intros n Hrev. unfold erasure_bits, reversible in *.
  apply Nat.log2_null. exact Hrev.
Qed.

(** Conversely, the only free collapses are the reversible ones: a strictly
    collapsing map (two or more witnesses on a base) always has a cost. *)
Theorem free_iff_reversible :
  forall n : nat, erasure_bits n = 0 <-> reversible n.
Proof.
  intro n. unfold erasure_bits, reversible. apply Nat.log2_null.
Qed.

(** ** Landauer: any genuine collapse costs at least one bit of erasure. *)
Theorem irreversible_costs_at_least_one_bit :
  forall n : nat, 2 <= n -> 1 <= erasure_bits n.
Proof.
  intros n Hn. unfold erasure_bits.
  change 1 with (Nat.log2 2).
  apply Nat.log2_le_mono. exact Hn.
Qed.

(** Collapsing a larger fibre never costs less — erasure is monotone in the
    amount of information discarded. *)
Theorem erasure_monotone :
  forall n m : nat, n <= m -> erasure_bits n <= erasure_bits m.
Proof.
  intros n m H. unfold erasure_bits. apply Nat.log2_le_mono. exact H.
Qed.

(** The witness of an echo over a one-element fibre is recoverable from the
    base, hence reversible and free — the type-level keystone (Echo.v's
    total-space equivalence) cashed out thermodynamically. *)
Corollary singleton_echo_is_free : erasure_bits 1 = 0.
Proof. apply bennett_reversible_is_free. unfold reversible. apply Nat.le_refl. Qed.
