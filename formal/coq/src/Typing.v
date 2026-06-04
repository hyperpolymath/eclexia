(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)
(* Type System Soundness Proofs *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
(* PeanoNat provides the boolean nat comparisons [=?], [<?], [<=?]
   (Nat.eqb / Nat.ltb / Nat.leb) and their [nat_scope] notations used
   by the small-step comparison rules below. Without it the comparison
   notations are unbound on Coq 8.18. *)
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(** * Type System Soundness for Eclexia

    This module formalizes the type soundness of Eclexia's core type system,
    proving Progress and Preservation theorems.
*)

(** ** Syntax *)

(** Types *)
Inductive ty : Type :=
  | TInt : ty
  | TFloat : ty
  | TBool : ty
  | TString : ty
  | TUnit : ty
  | TFun : ty -> ty -> ty
  | TDimensional : dimension -> ty
  | TOption : ty -> ty
  | TResult : ty -> ty -> ty

with dimension : Type :=
  | DScalar : dimension
  | DEnergy : dimension
  | DTime : dimension
  | DMass : dimension
  | DLength : dimension
  | DProduct : dimension -> dimension -> dimension
  | DQuotient : dimension -> dimension -> dimension
  | DPower : dimension -> nat -> dimension.

(** Expressions *)
Inductive expr : Type :=
  | EInt : nat -> expr
  | EFloat : nat -> expr  (* Simplified *)
  | EBool : bool -> expr
  | EVar : string -> expr
  | ELet : string -> expr -> expr -> expr
  | EFun : string -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | EBinOp : binop -> expr -> expr -> expr
  | EDimLit : nat -> dimension -> expr

with binop : Type :=
  | OpAdd | OpSub | OpMul | OpDiv
  | OpEq | OpLt | OpGt
  | OpAnd | OpOr.

(** Values *)
Inductive value : expr -> Prop :=
  | VInt : forall n, value (EInt n)
  | VFloat : forall n, value (EFloat n)
  | VBool : forall b, value (EBool b)
  | VFun : forall x T e, value (EFun x T e)
  | VDimLit : forall n d, value (EDimLit n d).

(** ** Typing Context *)

Definition context := list (string * ty).

Fixpoint lookup (x : string) (ctx : context) : option ty :=
  match ctx with
  | [] => None
  | (y, T) :: ctx' =>
      if String.eqb x y then Some T else lookup x ctx'
  end.

(** ** Typing Relation *)

Reserved Notation "ctx '⊢' e '∈' T" (at level 40).

Inductive has_type : context -> expr -> ty -> Prop :=
  | TInt_typed : forall ctx n,
      ctx ⊢ EInt n ∈ TInt

  | TFloat_typed : forall ctx n,
      ctx ⊢ EFloat n ∈ TFloat

  | TBool_typed : forall ctx b,
      ctx ⊢ EBool b ∈ TBool

  | TVar_typed : forall ctx x T,
      lookup x ctx = Some T ->
      ctx ⊢ EVar x ∈ T

  | TLet_typed : forall ctx x e1 e2 T1 T2,
      ctx ⊢ e1 ∈ T1 ->
      ((x, T1) :: ctx) ⊢ e2 ∈ T2 ->
      ctx ⊢ ELet x e1 e2 ∈ T2

  | TFun_typed : forall ctx x T1 T2 e,
      ((x, T1) :: ctx) ⊢ e ∈ T2 ->
      ctx ⊢ EFun x T1 e ∈ TFun T1 T2

  | TApp_typed : forall ctx e1 e2 T1 T2,
      ctx ⊢ e1 ∈ TFun T1 T2 ->
      ctx ⊢ e2 ∈ T1 ->
      ctx ⊢ EApp e1 e2 ∈ T2

  | TIf_typed : forall ctx e1 e2 e3 T,
      ctx ⊢ e1 ∈ TBool ->
      ctx ⊢ e2 ∈ T ->
      ctx ⊢ e3 ∈ T ->
      ctx ⊢ EIf e1 e2 e3 ∈ T

  | TBinOp_Int_typed : forall ctx e1 e2 op,
      (op = OpAdd \/ op = OpSub \/ op = OpMul \/ op = OpDiv) ->
      ctx ⊢ e1 ∈ TInt ->
      ctx ⊢ e2 ∈ TInt ->
      ctx ⊢ EBinOp op e1 e2 ∈ TInt

  | TBinOp_Bool_typed : forall ctx e1 e2 op,
      (op = OpAnd \/ op = OpOr) ->
      ctx ⊢ e1 ∈ TBool ->
      ctx ⊢ e2 ∈ TBool ->
      ctx ⊢ EBinOp op e1 e2 ∈ TBool

  | TBinOp_Cmp_typed : forall ctx e1 e2 op,
      (op = OpEq \/ op = OpLt \/ op = OpGt) ->
      ctx ⊢ e1 ∈ TInt ->
      ctx ⊢ e2 ∈ TInt ->
      ctx ⊢ EBinOp op e1 e2 ∈ TBool

  | TDimLit_typed : forall ctx n d,
      ctx ⊢ EDimLit n d ∈ TDimensional d

where "ctx '⊢' e '∈' T" := (has_type ctx e T).

(** ** Dimensional Typing Rules *)

(** Dimensional addition: same dimension *)
Inductive dim_add_type : dimension -> dimension -> dimension -> Prop :=
  | DimAdd_Same : forall d,
      dim_add_type d d d.

(** Dimensional multiplication: product *)
Inductive dim_mul_type : dimension -> dimension -> dimension -> Prop :=
  | DimMul : forall d1 d2,
      dim_mul_type d1 d2 (DProduct d1 d2).

(** Dimensional division: quotient *)
Inductive dim_div_type : dimension -> dimension -> dimension -> Prop :=
  | DimDiv : forall d1 d2,
      dim_div_type d1 d2 (DQuotient d1 d2).

(** Extended typing for dimensional operations *)
Inductive has_type_dim : context -> expr -> ty -> Prop :=
  | TDimAdd_typed : forall ctx e1 e2 d,
      ctx ⊢ e1 ∈ TDimensional d ->
      ctx ⊢ e2 ∈ TDimensional d ->
      has_type_dim ctx (EBinOp OpAdd e1 e2) (TDimensional d)

  | TDimMul_typed : forall ctx e1 e2 d1 d2 d3,
      ctx ⊢ e1 ∈ TDimensional d1 ->
      ctx ⊢ e2 ∈ TDimensional d2 ->
      dim_mul_type d1 d2 d3 ->
      has_type_dim ctx (EBinOp OpMul e1 e2) (TDimensional d3)

  | TDimDiv_typed : forall ctx e1 e2 d1 d2 d3,
      ctx ⊢ e1 ∈ TDimensional d1 ->
      ctx ⊢ e2 ∈ TDimensional d2 ->
      dim_div_type d1 d2 d3 ->
      has_type_dim ctx (EBinOp OpDiv e1 e2) (TDimensional d3).

(** ** Operational Semantics *)

(** Substitution *)
Fixpoint subst (x : string) (v : expr) (e : expr) : expr :=
  match e with
  | EVar y => if String.eqb x y then v else EVar y
  | EInt n => EInt n
  | EFloat n => EFloat n
  | EBool b => EBool b
  | ELet y e1 e2 =>
      let e1' := subst x v e1 in
      let e2' := if String.eqb x y then e2 else subst x v e2 in
      ELet y e1' e2'
  | EFun y T e' =>
      if String.eqb x y then EFun y T e' else EFun y T (subst x v e')
  | EApp e1 e2 =>
      EApp (subst x v e1) (subst x v e2)
  | EIf e1 e2 e3 =>
      EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | EBinOp op e1 e2 =>
      EBinOp op (subst x v e1) (subst x v e2)
  | EDimLit n d => EDimLit n d
  end.

(** Small-step operational semantics *)
Reserved Notation "e '→' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
  | STApp : forall x T e v,
      value v ->
      EApp (EFun x T e) v → subst x v e

  | STAppFun : forall e1 e1' e2,
      e1 → e1' ->
      EApp e1 e2 → EApp e1' e2

  | STAppArg : forall v e2 e2',
      value v ->
      e2 → e2' ->
      EApp v e2 → EApp v e2'

  | STLet : forall x v e,
      value v ->
      ELet x v e → subst x v e

  | STLetStep : forall x e1 e1' e2,
      e1 → e1' ->
      ELet x e1 e2 → ELet x e1' e2

  | STIfTrue : forall e2 e3,
      EIf (EBool true) e2 e3 → e2

  | STIfFalse : forall e2 e3,
      EIf (EBool false) e2 e3 → e3

  | STIfStep : forall e1 e1' e2 e3,
      e1 → e1' ->
      EIf e1 e2 e3 → EIf e1' e2 e3

  (* Arithmetic *)
  | STBinOpInt : forall op n1 n2 n3,
      (op = OpAdd /\ n3 = n1 + n2) \/
      (op = OpSub /\ n3 = n1 - n2) \/
      (op = OpMul /\ n3 = n1 * n2) \/
      (op = OpDiv /\ n3 = Nat.div n1 n2) ->
      EBinOp op (EInt n1) (EInt n2) → EInt n3

  (* Boolean operations *)
  | STBinOpBool : forall op b1 b2 b3,
      (op = OpAnd /\ b3 = andb b1 b2) \/
      (op = OpOr /\ b3 = orb b1 b2) ->
      EBinOp op (EBool b1) (EBool b2) → EBool b3

  (* Comparison operations *)
  | STBinOpCmp : forall op n1 n2 b,
      (op = OpEq /\ b = (n1 =? n2)) \/
      (op = OpLt /\ b = (n1 <? n2)) \/
      (op = OpGt /\ b = (n2 <? n1)) ->
      EBinOp op (EInt n1) (EInt n2) → EBool b

  | STBinOpLeft : forall op e1 e1' e2,
      e1 → e1' ->
      EBinOp op e1 e2 → EBinOp op e1' e2

  | STBinOpRight : forall op v e2 e2',
      value v ->
      e2 → e2' ->
      EBinOp op v e2 → EBinOp op v e2'

where "e '→' e'" := (step e e').

(** Multi-step relation *)
Inductive multi_step : expr -> expr -> Prop :=
  | MSRefl : forall e, multi_step e e
  | MSStep : forall e1 e2 e3,
      e1 → e2 ->
      multi_step e2 e3 ->
      multi_step e1 e3.

Notation "e '→*' e'" := (multi_step e e') (at level 40).

(** ** Lookup monotonicity under context extension *)

(** If [ctx] is included in [ctx'] as a partial map (every successful
    lookup in [ctx] agrees in [ctx']), the inclusion is preserved when
    both contexts are extended with the same binding. This is the one
    structural fact the weakening induction needs at the binder cases
    ([TLet_typed], [TFun_typed]). *)
Lemma lookup_incl_cons : forall x T1 ctx ctx',
  (forall y S, lookup y ctx = Some S -> lookup y ctx' = Some S) ->
  (forall y S, lookup y ((x, T1) :: ctx) = Some S ->
               lookup y ((x, T1) :: ctx') = Some S).
Proof.
  intros x T1 ctx ctx' Hincl y S.
  simpl. destruct (String.eqb y x).
  - intro H; exact H.
  - intro H; apply Hincl; exact H.
Qed.

(** ** General weakening (lookup-monotone)

    Typing is preserved along any partial-map inclusion of contexts,
    proved by induction on the typing derivation. The original
    [weakening] lemma below is the special case [ctx = []]. *)
Lemma weakening_gen : forall ctx e T,
  ctx ⊢ e ∈ T ->
  forall ctx',
    (forall y S, lookup y ctx = Some S -> lookup y ctx' = Some S) ->
    ctx' ⊢ e ∈ T.
Proof.
  intros ctx e T Htyped.
  induction Htyped; intros ctx' Hincl;
    eauto 10 using TInt_typed, TFloat_typed, TBool_typed, TVar_typed,
                   TLet_typed, TFun_typed, TApp_typed, TIf_typed,
                   TBinOp_Int_typed, TBinOp_Bool_typed, TBinOp_Cmp_typed,
                   TDimLit_typed, lookup_incl_cons.
Qed.

(** ** Weakening Lemma

    A term typeable in the empty context is typeable in any context.
    The [value e] hypothesis is retained for backward compatibility
    with existing callers; the result in fact holds for every term
    typeable in [[]], because the empty context is vacuously included
    in every context. The previous proof discharged the function-value
    case with a bare [assumption], which cannot succeed: a closed
    function's body is typed under [(x,T1)::[]] but weakening demands
    it under [(x,T1)::ctx]. [weakening_gen] supplies exactly that. *)
Lemma weakening : forall ctx e T,
  [] ⊢ e ∈ T ->
  value e ->
  ctx ⊢ e ∈ T.
Proof.
  intros ctx e T Htyped _.
  apply (weakening_gen [] e T Htyped).
  intros y S Hlook. simpl in Hlook. discriminate.
Qed.

(** ** Context exchange and shadowing (corollaries of [weakening_gen])

    These are the structural facts the substitution lemma needs at the
    binder cases. Both are instances of [weakening_gen]: two contexts
    that agree as partial maps type the same terms. *)

(** Two adjacent bindings with distinct keys may be swapped. *)
Lemma context_exchange : forall x1 T1' x2 T2' ctx e T,
  x1 <> x2 ->
  ((x1, T1') :: (x2, T2') :: ctx) ⊢ e ∈ T ->
  ((x2, T2') :: (x1, T1') :: ctx) ⊢ e ∈ T.
Proof.
  intros x1 T1' x2 T2' ctx e T Hne H.
  apply (weakening_gen _ _ _ H).
  intros y S. simpl.
  destruct (String.eqb y x1) eqn:E1; destruct (String.eqb y x2) eqn:E2;
    intro HL; try exact HL.
  exfalso. apply Hne.
  apply String.eqb_eq in E1. apply String.eqb_eq in E2. congruence.
Qed.

(** An inner binding shadowed by a later one with the same key is
    redundant and may be dropped. *)
Lemma context_shadow : forall x T1' T2' ctx e T,
  ((x, T1') :: (x, T2') :: ctx) ⊢ e ∈ T ->
  ((x, T1') :: ctx) ⊢ e ∈ T.
Proof.
  intros x T1' T2' ctx e T H.
  apply (weakening_gen _ _ _ H).
  intros y S. simpl.
  destruct (String.eqb y x) eqn:E; intro HL; exact HL.
Qed.

(** ** Substitution Lemma *)

Lemma subst_preserves_typing : forall x v e T1 T2 ctx,
  value v ->
  [] ⊢ v ∈ T1 ->
  ((x, T1) :: ctx) ⊢ e ∈ T2 ->
  ctx ⊢ subst x v e ∈ T2.
Proof.
  intros x v e T1 T2 ctx Hval Hv Htyped.
  generalize dependent ctx.
  generalize dependent T2.
  induction e; intros T2 ctx Htyped; simpl; inversion Htyped; subst.
  - (* EInt *)
    apply TInt_typed.
  - (* EFloat *)
    apply TFloat_typed.
  - (* EBool *)
    apply TBool_typed.
  - (* EVar *)
    (* [lookup] compares [String.eqb s x] but [subst] compares
       [String.eqb x s]; reconcile the two orders with [eqb_sym] so a
       single case split decides both the goal and the hypothesis. *)
    simpl in H1. rewrite String.eqb_sym in H1.
    destruct (String.eqb x s) eqn:Heq.
    + (* x = s: the variable is the one being substituted *)
      injection H1 as H1. subst T2.
      apply (weakening ctx v T1 Hv Hval).
    + (* x <> s: the variable is preserved *)
      apply TVar_typed. exact H1.
  - (* ELet *)
    (* [TLet_typed]'s intermediate type is not in its conclusion, so we
       use [eapply ...; [ .. | .. ]] to share the resulting existential
       between the two premises rather than shelving it. *)
    destruct (String.eqb x s) eqn:Heq.
    + (* x = s: the let-binder shadows x, so e2 is not substituted *)
      apply String.eqb_eq in Heq. subst s.
      eapply TLet_typed;
        [ apply IHe1; eassumption
        | eapply context_shadow; eassumption ].
    + (* x <> s: substitute into e2 under the swapped binder *)
      eapply TLet_typed;
        [ apply IHe1; eassumption
        | apply IHe2; apply context_exchange;
            [ apply String.eqb_neq in Heq; intro Hc; apply Heq; symmetry; exact Hc
            | eassumption ] ].
  - (* EFun *)
    destruct (String.eqb x s) eqn:Heq.
    + (* x = s: parameter shadows x, no substitution in the body *)
      apply String.eqb_eq in Heq. subst s.
      apply TFun_typed. eapply context_shadow. eassumption.
    + (* x <> s: substitute into the body under the swapped binder *)
      apply TFun_typed. apply IHe. apply context_exchange.
      * apply String.eqb_neq in Heq. intro Hc. apply Heq. symmetry. exact Hc.
      * eassumption.
  - (* EApp *)
    eapply TApp_typed.
    + apply IHe1. eassumption.
    + apply IHe2. assumption.
  - (* EIf *)
    apply TIf_typed.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
    + apply IHe3. assumption.
  - (* EBinOp Int *)
    eapply TBinOp_Int_typed; eauto.
  - (* EBinOp Bool *)
    eapply TBinOp_Bool_typed; eauto.
  - (* EBinOp Cmp *)
    eapply TBinOp_Cmp_typed; eauto.
  - (* EDimLit *)
    apply TDimLit_typed.
Qed.

(** ** Canonical forms

    A value of a given type has the expected head shape. These three
    lemmas drive the value cases of [progress]: each inverts the value
    and then the typing derivation, so the constructors that disagree
    with the type are discharged automatically. *)
Lemma canonical_forms_bool : forall ctx e,
  ctx ⊢ e ∈ TBool -> value e -> exists b, e = EBool b.
Proof.
  intros ctx e HT Hv. inversion Hv; subst; inversion HT; subst; eexists; reflexivity.
Qed.

Lemma canonical_forms_int : forall ctx e,
  ctx ⊢ e ∈ TInt -> value e -> exists n, e = EInt n.
Proof.
  intros ctx e HT Hv. inversion Hv; subst; inversion HT; subst; eexists; reflexivity.
Qed.

Lemma canonical_forms_fun : forall ctx e T1 T2,
  ctx ⊢ e ∈ TFun T1 T2 -> value e -> exists x body, e = EFun x T1 body.
Proof.
  intros ctx e T1 T2 HT Hv.
  inversion Hv; subst; inversion HT; subst; eexists; eexists; reflexivity.
Qed.

(** ** Type Soundness *)

(** Progress: Well-typed expressions either are values or can step *)
Theorem progress : forall e T,
  [] ⊢ e ∈ T ->
  value e \/ exists e', e → e'.
Proof.
  intros e T Htyped.
  remember [] as ctx.
  induction Htyped; subst.
  - (* TInt *) left. apply VInt.
  - (* TFloat *) left. apply VFloat.
  - (* TBool *) left. apply VBool.
  - (* TVar *) discriminate.  (* Empty context *)
  - (* TLet *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + (* e1 is value *) exists (subst x e1 e2). apply STLet. assumption.
    + (* e1 steps *) exists (ELet x e1' e2). apply STLetStep. assumption.
  - (* TFun *) left. apply VFun.
  - (* TApp *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + (* e1 is value *)
      destruct IHHtyped2 as [Hval2 | [e2' Hstep2]]; auto.
      * (* e2 is value: e1 is a function by canonical forms *)
        match goal with
        | [ HT : _ ⊢ e1 ∈ TFun _ _ |- _ ] =>
            destruct (canonical_forms_fun _ _ _ _ HT Hval1) as [y [body Hb]]
        end. subst e1.
        eexists. apply STApp. assumption.
      * (* e2 steps *)
        exists (EApp e1 e2'). apply STAppArg; assumption.
    + (* e1 steps *)
      exists (EApp e1' e2). apply STAppFun. assumption.
  - (* TIf *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + (* e1 is value: it is a boolean by canonical forms *)
      match goal with
      | [ HT : _ ⊢ e1 ∈ TBool |- _ ] =>
          destruct (canonical_forms_bool _ _ HT Hval1) as [b Hb]
      end. subst e1.
      destruct b.
      * exists e2. apply STIfTrue.
      * exists e3. apply STIfFalse.
    + (* e1 steps *)
      exists (EIf e1' e2 e3). apply STIfStep. assumption.
  - (* TBinOp Int *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + destruct IHHtyped2 as [Hval2 | [e2' Hstep2]]; auto.
      * (* Both values: both integers by canonical forms *)
        match goal with
        | [ HT : _ ⊢ e1 ∈ TInt |- _ ] =>
            destruct (canonical_forms_int _ _ HT Hval1) as [n Hn1]
        end. subst e1.
        match goal with
        | [ HT : _ ⊢ e2 ∈ TInt |- _ ] =>
            destruct (canonical_forms_int _ _ HT Hval2) as [n0 Hn2]
        end. subst e2.
        destruct H as [HAdd | [HSub | [HMul | HDiv]]]; subst.
        { exists (EInt (n + n0)). apply STBinOpInt. left. split; reflexivity. }
        { exists (EInt (n - n0)). apply STBinOpInt. right. left. split; reflexivity. }
        { exists (EInt (n * n0)). apply STBinOpInt. right. right. left. split; reflexivity. }
        { exists (EInt (Nat.div n n0)). apply STBinOpInt. right. right. right. split; reflexivity. }
      * (* e2 steps *)
        exists (EBinOp op e1 e2'). apply STBinOpRight; assumption.
    + (* e1 steps *)
      exists (EBinOp op e1' e2). apply STBinOpLeft. assumption.
  - (* TBinOp Bool *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + destruct IHHtyped2 as [Hval2 | [e2' Hstep2]]; auto.
      * (* Both values: both booleans by canonical forms *)
        match goal with
        | [ HT : _ ⊢ e1 ∈ TBool |- _ ] =>
            destruct (canonical_forms_bool _ _ HT Hval1) as [b Hb1]
        end. subst e1.
        match goal with
        | [ HT : _ ⊢ e2 ∈ TBool |- _ ] =>
            destruct (canonical_forms_bool _ _ HT Hval2) as [b0 Hb2]
        end. subst e2.
        destruct H as [HAnd | HOr]; subst.
        { exists (EBool (andb b b0)). apply STBinOpBool. left. split; reflexivity. }
        { exists (EBool (orb b b0)). apply STBinOpBool. right. split; reflexivity. }
      * exists (EBinOp op e1 e2'). apply STBinOpRight; assumption.
    + exists (EBinOp op e1' e2). apply STBinOpLeft. assumption.
  - (* TBinOp Cmp *)
    right.
    destruct IHHtyped1 as [Hval1 | [e1' Hstep1]]; auto.
    + destruct IHHtyped2 as [Hval2 | [e2' Hstep2]]; auto.
      * (* Both values: both integers by canonical forms *)
        match goal with
        | [ HT : _ ⊢ e1 ∈ TInt |- _ ] =>
            destruct (canonical_forms_int _ _ HT Hval1) as [n Hn1]
        end. subst e1.
        match goal with
        | [ HT : _ ⊢ e2 ∈ TInt |- _ ] =>
            destruct (canonical_forms_int _ _ HT Hval2) as [n0 Hn2]
        end. subst e2.
        destruct H as [HEq | [HLt | HGt]]; subst.
        { exists (EBool (n =? n0)). apply STBinOpCmp. left. split; reflexivity. }
        { exists (EBool (n <? n0)). apply STBinOpCmp. right. left. split; reflexivity. }
        { exists (EBool (n0 <? n)). apply STBinOpCmp. right. right. split; reflexivity. }
      * exists (EBinOp op e1 e2'). apply STBinOpRight; assumption.
    + exists (EBinOp op e1' e2). apply STBinOpLeft. assumption.
  - (* TDimLit *)
    left. apply VDimLit.
Qed.

(** Preservation: If e : T and e → e', then e' : T *)
Theorem preservation : forall e e' T,
  [] ⊢ e ∈ T ->
  e → e' ->
  [] ⊢ e' ∈ T.
Proof.
  (* Induction on the step relation. The step's shape pins the redex,
     [inversion Htyped] recovers the typing premises, and the residual
     goals are discharged uniformly:
       - if-true/false: the taken branch's typing hypothesis;
       - beta (application): invert the function's typing, then the
         substitution lemma;
       - let: the substitution lemma directly;
       - congruence: the matching typing constructor + the IH (found by
         [eauto] over all constructors, which also re-types literal
         results such as [EInt n3 : TInt]);
       - spurious binop typing subcases ([inversion Htyped] offers an
         Int/Bool/Cmp reading for every [EBinOp]): a literal cannot have
         the wrong base type, and the operator tag sets are disjoint. *)
  intros e e' T Htyped Hstep. generalize dependent T.
  (* [Tres] avoids a name clash with the [T] bound by step constructors
     such as [STApp] (the function's domain annotation). *)
  induction Hstep; intros Tres Htyped; inversion Htyped; subst;
    try (solve [assumption]);
    try (solve [ match goal with
                 | [ Hf : _ ⊢ EFun _ _ _ ∈ _ |- _ ] => inversion Hf; subst
                 end;
                 eapply subst_preserves_typing; eauto ]);
    try (solve [eapply subst_preserves_typing; eauto]);
    try (solve [eauto 8 using TInt_typed, TFloat_typed, TBool_typed,
                  TVar_typed, TLet_typed, TFun_typed, TApp_typed, TIf_typed,
                  TBinOp_Int_typed, TBinOp_Bool_typed, TBinOp_Cmp_typed,
                  TDimLit_typed]);
    try (solve [ exfalso;
                 repeat match goal with
                        | [ H : _ ⊢ EInt _ ∈ TBool |- _ ] => inversion H
                        | [ H : _ ⊢ EBool _ ∈ TInt |- _ ] => inversion H
                        | [ H : _ ⊢ EInt _ ∈ TFun _ _ |- _ ] => inversion H
                        | [ H : _ ⊢ EBool _ ∈ TFun _ _ |- _ ] => inversion H
                        | [ H : _ \/ _ |- _ ] => destruct H
                        | [ H : _ /\ _ |- _ ] => destruct H
                        end;
                 subst; discriminate ]).
Qed.

(** Preservation lifts to the reflexive-transitive closure. Stated as
    its own lemma so the typing hypothesis is generalised correctly
    across the [multi_step] induction (inducting on [Hmulti] with the
    typing left in the context would silently fix the start term). *)
Lemma multi_preservation : forall e e' T,
  [] ⊢ e ∈ T ->
  e →* e' ->
  [] ⊢ e' ∈ T.
Proof.
  intros e e' T Htyped Hmulti. revert T Htyped.
  induction Hmulti as [e | e1 e2 e3 Hstep Hmulti IH]; intros T Htyped.
  - assumption.
  - apply IH. eapply preservation; eauto.
Qed.

(** ** Type Soundness (Combined) *)

(** If e : T and e →* e', then either e' is a value or e' can step *)
Theorem soundness : forall e e' T,
  [] ⊢ e ∈ T ->
  e →* e' ->
  value e' \/ exists e'', e' → e''.
Proof.
  intros e e' T Htyped Hmulti.
  apply (progress e' T).
  eapply multi_preservation; eauto.
Qed.

(** ** Dimensional Type Safety *)

(** Dimension errors cannot occur at runtime *)
Theorem dimensional_safety : forall e d,
  [] ⊢ e ∈ TDimensional d ->
  forall e', e →* e' -> value e' ->
  exists n, e' = EDimLit n d.
Proof.
  intros e d Htyped e' Hmulti Hval.
  (* Typing is preserved along the reduction, so e' still has type
     TDimensional d; a value of that type must be a dimensioned
     literal with the same dimension. *)
  assert (Htyped' : [] ⊢ e' ∈ TDimensional d)
    by (eapply multi_preservation; eauto).
  inversion Hval; subst; inversion Htyped'; subst.
  eexists. reflexivity.
Qed.

(** ** Summary *)

(**
   We have formalized:
   1. Core type system with dimensional types
   2. Operational semantics (small-step)
   3. Progress theorem (well-typed programs don't get stuck)
   4. Preservation theorem (types are preserved by evaluation)
   5. Type soundness (combined progress + preservation)
   6. Dimensional type safety (dimension errors prevented)

   These proofs establish that Eclexia's type system is sound and
   that dimensional type errors cannot occur at runtime in well-typed programs.
*)
