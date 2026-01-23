(** * Typing.v - Type system for Eclexia *)
(** SPDX-License-Identifier: AGPL-3.0-or-later *)
(** SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.
Require Import Syntax.

(** * Type Environments *)

(** Type context (de Bruijn indices) *)
Definition ctx := list ty.

(** Lookup type in context *)
Fixpoint lookup (n : nat) (Γ : ctx) : option ty :=
  match Γ with
  | [] => None
  | T :: Γ' => if Nat.eqb n 0 then Some T else lookup (n - 1) Γ'
  end.

(** * Type Substitution *)

(** Substitute type variable X with U in type T *)
Fixpoint ty_subst (X : nat) (U : ty) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TBool => TBool
  | TInt => TInt
  | TFloat => TFloat
  | TString => TString
  | TVar Y => if Nat.eqb X Y then U else TVar Y
  | TArr T1 T2 => TArr (ty_subst X U T1) (ty_subst X U T2)
  | TProd T1 T2 => TProd (ty_subst X U T1) (ty_subst X U T2)
  | TSum T1 T2 => TSum (ty_subst X U T1) (ty_subst X U T2)
  | TForall T' => TForall (ty_subst (S X) U T')
  | TExists T' => TExists (ty_subst (S X) U T')
  | TMu T' => TMu (ty_subst (S X) U T')
  | TResource rk d => TResource rk d
  | TConstrained T' C => TConstrained (ty_subst X U T') C
  | TEffectful T' E => TEffectful (ty_subst X U T') E
  end.

(** * Kinding Judgment *)

(** Well-formed types (kinding) *)
Inductive has_kind : ctx -> ty -> Prop :=
  | K_Unit : forall Γ,
      has_kind Γ TUnit
  | K_Bool : forall Γ,
      has_kind Γ TBool
  | K_Int : forall Γ,
      has_kind Γ TInt
  | K_Float : forall Γ,
      has_kind Γ TFloat
  | K_String : forall Γ,
      has_kind Γ TString
  | K_Var : forall Γ X,
      X < length Γ ->
      has_kind Γ (TVar X)
  | K_Arr : forall Γ T1 T2,
      has_kind Γ T1 ->
      has_kind Γ T2 ->
      has_kind Γ (TArr T1 T2)
  | K_Prod : forall Γ T1 T2,
      has_kind Γ T1 ->
      has_kind Γ T2 ->
      has_kind Γ (TProd T1 T2)
  | K_Sum : forall Γ T1 T2,
      has_kind Γ T1 ->
      has_kind Γ T2 ->
      has_kind Γ (TSum T1 T2)
  | K_Forall : forall Γ T,
      has_kind (TUnit :: Γ) T ->
      has_kind Γ (TForall T)
  | K_Exists : forall Γ T,
      has_kind (TUnit :: Γ) T ->
      has_kind Γ (TExists T)
  | K_Mu : forall Γ T,
      has_kind (TUnit :: Γ) T ->
      has_kind Γ (TMu T)
  | K_Resource : forall Γ rk d,
      has_kind Γ (TResource rk d)
  | K_Constrained : forall Γ T C,
      has_kind Γ T ->
      has_kind Γ (TConstrained T C)
  | K_Effectful : forall Γ T E,
      has_kind Γ T ->
      has_kind Γ (TEffectful T E).

(** * Typing Judgment *)

(** Main typing relation *)
Inductive has_type : ctx -> tm -> ty -> Prop :=
  | T_Var : forall Γ x T,
      lookup x Γ = Some T ->
      has_type Γ (tvar x) T
  | T_Unit : forall Γ,
      has_type Γ tunit TUnit
  | T_Bool : forall Γ b,
      has_type Γ (tbool b) TBool
  | T_Int : forall Γ n,
      has_type Γ (tint n) TInt
  | T_Float : forall Γ r,
      has_type Γ (tfloat r) TFloat
  | T_String : forall Γ s,
      has_type Γ (tstring s) TString
  | T_Abs : forall Γ T1 T2 t,
      has_type (T1 :: Γ) t T2 ->
      has_type Γ (tabs T1 t) (TArr T1 T2)
  | T_App : forall Γ t1 t2 T1 T2,
      has_type Γ t1 (TArr T1 T2) ->
      has_type Γ t2 T1 ->
      has_type Γ (tapp t1 t2) T2
  | T_TAbs : forall Γ t T,
      has_type (TUnit :: Γ) t T ->
      has_type Γ (tTabs t) (TForall T)
  | T_TApp : forall Γ t T1 T2,
      has_type Γ t (TForall T1) ->
      has_kind Γ T2 ->
      has_type Γ (tTapp t T2) (ty_subst 0 T2 T1)
  | T_Let : forall Γ t1 t2 T1 T2,
      has_type Γ t1 T1 ->
      has_type (T1 :: Γ) t2 T2 ->
      has_type Γ (tlet t1 t2) T2
  | T_Pair : forall Γ t1 t2 T1 T2,
      has_type Γ t1 T1 ->
      has_type Γ t2 T2 ->
      has_type Γ (tpair t1 t2) (TProd T1 T2)
  | T_Fst : forall Γ t T1 T2,
      has_type Γ t (TProd T1 T2) ->
      has_type Γ (tfst t) T1
  | T_Snd : forall Γ t T1 T2,
      has_type Γ t (TProd T1 T2) ->
      has_type Γ (tsnd t) T2
  | T_Inl : forall Γ t T1 T2,
      has_type Γ t T1 ->
      has_type Γ (tinl T2 t) (TSum T1 T2)
  | T_Inr : forall Γ t T1 T2,
      has_type Γ t T2 ->
      has_type Γ (tinr T1 t) (TSum T1 T2)
  | T_Case : forall Γ t t1 t2 T1 T2 T,
      has_type Γ t (TSum T1 T2) ->
      has_type (T1 :: Γ) t1 T ->
      has_type (T2 :: Γ) t2 T ->
      has_type Γ (tcase t t1 t2) T
  | T_Fold : forall Γ t T,
      has_type Γ t (ty_subst 0 (TMu T) T) ->
      has_type Γ (tfold (TMu T) t) (TMu T)
  | T_Unfold : forall Γ t T,
      has_type Γ t (TMu T) ->
      has_type Γ (tunfold t) (ty_subst 0 (TMu T) T)
  | T_Resource : forall Γ q rk d,
      has_type Γ (tresource q rk d) (TResource rk d)
  | T_ResAdd : forall Γ t1 t2 rk d,
      has_type Γ t1 (TResource rk d) ->
      has_type Γ t2 (TResource rk d) ->
      has_type Γ (tresadd t1 t2) (TResource rk d)
  | T_ResMul : forall Γ t1 t2 rk d1 d2,
      has_type Γ t1 (TResource rk d1) ->
      has_type Γ t2 (TResource rk d2) ->
      has_type Γ (tresmul t1 t2) (TResource rk (dim_mul d1 d2))
  | T_ResDiv : forall Γ t1 t2 rk d1 d2,
      has_type Γ t1 (TResource rk d1) ->
      has_type Γ t2 (TResource rk d2) ->
      has_type Γ (tresdiv t1 t2) (TResource rk (dim_div d1 d2))
  | T_Adaptive : forall Γ C objs sols T,
      (* TODO: Add solution typing constraint *)
      has_type Γ (tadaptive C objs sols) T
  | T_Handle : forall Γ t handlers ret T,
      has_type Γ t T ->
      (* TODO: Add handler typing constraints *)
      has_type Γ (thandle t handlers ret) T.

(** * Basic Typing Properties *)

(** Weakening lemma *)
Lemma weakening : forall Γ1 Γ2 t T,
  has_type Γ1 t T ->
  has_type (Γ1 ++ Γ2) t T.
Proof.
  (* TODO: Proof by induction on typing derivation *)
Admitted.

(** Type uniqueness *)
Lemma type_uniqueness : forall Γ t T1 T2,
  has_type Γ t T1 ->
  has_type Γ t T2 ->
  T1 = T2.
Proof.
  (* TODO: Proof by induction on typing derivations *)
Admitted.
