(** * Syntax.v - Core calculus syntax for Eclexia *)
(** SPDX-License-Identifier: AGPL-3.0-or-later *)
(** SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

Open Scope Z_scope.
Open Scope Q_scope.

(** * Dimensions and Resource Kinds *)

(** SI base dimensions *)
Inductive BaseDim : Type :=
  | DimM      (** Mass (kg) *)
  | DimL      (** Length (m) *)
  | DimT      (** Time (s) *)
  | DimI      (** Electric current (A) *)
  | DimTheta  (** Temperature (K) *)
  | DimN      (** Amount of substance (mol) *)
  | DimJ.     (** Luminous intensity (cd) *)

(** Decidable equality for base dimensions *)
Lemma BaseDim_eq_dec : forall (d1 d2 : BaseDim), {d1 = d2} + {d1 <> d2}.
Proof.
  decide equality.
Defined.

(** Dimensions as integer exponent vectors *)
Definition Dim := BaseDim -> Z.

(** Dimensionless (identity) *)
Definition dim_one : Dim := fun _ => 0%Z.

(** Single base dimension with exponent 1 *)
Definition dim_base (b : BaseDim) : Dim :=
  fun b' => if BaseDim_eq_dec b b' then 1%Z else 0%Z.

(** Dimension multiplication (add exponents) *)
Definition dim_mul (d1 d2 : Dim) : Dim :=
  fun b => (d1 b + d2 b)%Z.

(** Dimension division (subtract exponents) *)
Definition dim_div (d1 d2 : Dim) : Dim :=
  fun b => (d1 b - d2 b)%Z.

(** Dimension inverse *)
Definition dim_inv (d : Dim) : Dim :=
  fun b => (- d b)%Z.

(** Dimension equality (pointwise equality) *)
Definition dim_eq (d1 d2 : Dim) : Prop :=
  forall b, d1 b = d2 b.

(** Dimension equality is an equivalence relation *)
Lemma dim_eq_refl : forall d, dim_eq d d.
Proof. unfold dim_eq; auto. Qed.

Lemma dim_eq_sym : forall d1 d2, dim_eq d1 d2 -> dim_eq d2 d1.
Proof. unfold dim_eq; auto. Qed.

Lemma dim_eq_trans : forall d1 d2 d3, dim_eq d1 d2 -> dim_eq d2 d3 -> dim_eq d1 d3.
Proof. unfold dim_eq; intros; congruence. Qed.

(** Dimension algebra laws *)
Lemma dim_mul_assoc : forall d1 d2 d3,
  dim_eq (dim_mul (dim_mul d1 d2) d3) (dim_mul d1 (dim_mul d2 d3)).
Proof.
  unfold dim_eq, dim_mul; intros; lia.
Qed.

Lemma dim_mul_comm : forall d1 d2,
  dim_eq (dim_mul d1 d2) (dim_mul d2 d1).
Proof.
  unfold dim_eq, dim_mul; intros; lia.
Qed.

Lemma dim_mul_one_l : forall d,
  dim_eq (dim_mul dim_one d) d.
Proof.
  unfold dim_eq, dim_mul, dim_one; intros; lia.
Qed.

Lemma dim_mul_one_r : forall d,
  dim_eq (dim_mul d dim_one) d.
Proof.
  unfold dim_eq, dim_mul, dim_one; intros; lia.
Qed.

Lemma dim_mul_inv_l : forall d,
  dim_eq (dim_mul (dim_inv d) d) dim_one.
Proof.
  unfold dim_eq, dim_mul, dim_inv, dim_one; intros; lia.
Qed.

Lemma dim_mul_inv_r : forall d,
  dim_eq (dim_mul d (dim_inv d)) dim_one.
Proof.
  unfold dim_eq, dim_mul, dim_inv, dim_one; intros; lia.
Qed.

(** * Resource Kinds *)

Inductive ResourceKind : Type :=
  | RKEnergy   (** Energy (Joules) *)
  | RKTime     (** Time (seconds) *)
  | RKMemory   (** Memory (bytes) *)
  | RKCarbon.  (** Carbon (gCO2e) *)

(** Decidable equality for resource kinds *)
Lemma ResourceKind_eq_dec : forall (r1 r2 : ResourceKind), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

(** * Types *)

(** Constraints on resources *)
Inductive constraint : Type :=
  | CTrue : constraint
  | CLt : ResourceKind -> Q -> constraint      (** r < q *)
  | CLe : ResourceKind -> Q -> constraint      (** r ≤ q *)
  | CEq : ResourceKind -> Q -> constraint      (** r = q *)
  | CGe : ResourceKind -> Q -> constraint      (** r ≥ q *)
  | CGt : ResourceKind -> Q -> constraint      (** r > q *)
  | CAnd : constraint -> constraint -> constraint.

(** Effects and Types are mutually recursive *)
Inductive effect : Type :=
  | EEmpty : effect
  | EOp : string -> ty -> ty -> effect
  | EUnion : effect -> effect -> effect

with ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TFloat : ty
  | TString : ty
  | TVar : nat -> ty                               (** Type variable (de Bruijn index) *)
  | TArr : ty -> ty -> ty                          (** Function type T1 → T2 *)
  | TProd : ty -> ty -> ty                         (** Product type T1 × T2 *)
  | TSum : ty -> ty -> ty                          (** Sum type T1 + T2 *)
  | TForall : ty -> ty                             (** Universal quantification ∀X.T *)
  | TExists : ty -> ty                             (** Existential quantification ∃X.T *)
  | TMu : ty -> ty                                 (** Recursive type μX.T *)
  | TResource : ResourceKind -> Dim -> ty          (** Resource type with dimension *)
  | TConstrained : ty -> constraint -> ty          (** Constrained type {T | C} *)
  | TEffectful : ty -> effect -> ty.               (** Effectful type T ! E *)

(** * Terms *)

(** Resource profiles for adaptive solutions *)
Record resource_profile : Type := Profile {
  energy_cost  : Q;
  time_cost    : Q;
  memory_cost  : Q;
  carbon_cost  : Q
}.

(** Optimization objectives *)
Inductive objective : Type :=
  | Minimize : ResourceKind -> objective
  | Maximize : ResourceKind -> objective.

(** Terms - standalone inductive (not mutually recursive) *)
Inductive tm : Type :=
  | tvar : nat -> tm                                       (** Variable (de Bruijn index) *)
  | tunit : tm                                             (** Unit literal () *)
  | tbool : bool -> tm                                     (** Boolean literal *)
  | tint : Z -> tm                                         (** Integer literal *)
  | tfloat : Q -> tm                                       (** Float literal (rational) *)
  | tstring : string -> tm                                 (** String literal *)
  | tabs : ty -> tm -> tm                                  (** Lambda abstraction λx:T.t *)
  | tapp : tm -> tm -> tm                                  (** Application t1 t2 *)
  | tTabs : tm -> tm                                       (** Type abstraction ΛX.t *)
  | tTapp : tm -> ty -> tm                                 (** Type application t [T] *)
  | tlet : tm -> tm -> tm                                  (** Let binding let x = t1 in t2 *)
  | tpair : tm -> tm -> tm                                 (** Pair (t1, t2) *)
  | tfst : tm -> tm                                        (** First projection fst t *)
  | tsnd : tm -> tm                                        (** Second projection snd t *)
  | tinl : ty -> tm -> tm                                  (** Left injection inl t *)
  | tinr : ty -> tm -> tm                                  (** Right injection inr t *)
  | tcase : tm -> tm -> tm -> tm                           (** Case analysis case t of ... *)
  | tfold : ty -> tm -> tm                                 (** Fold (for recursive types) *)
  | tunfold : tm -> tm                                     (** Unfold (for recursive types) *)
  | tresource : Q -> ResourceKind -> Dim -> tm             (** Resource literal 100J *)
  | tresadd : tm -> tm -> tm                               (** Resource addition *)
  | tresmul : tm -> tm -> tm                               (** Resource multiplication *)
  | tresdiv : tm -> tm -> tm                               (** Resource division *)
  | tadaptive : constraint -> list objective -> list (tm * tm * resource_profile) -> tm  (** Adaptive block (guard, body, profile) *)
  | thandle : tm -> list (string * tm) -> tm -> tm.        (** Handle effect (handlers, return continuation) *)

(** Helper definitions for solutions and handlers *)
Definition solution := (tm * tm * resource_profile)%type.
Definition handler := (list (string * tm) * tm)%type.

(** * Values *)

(** Predicate for closed terms (no free variables) *)
Fixpoint closed (n : nat) (t : tm) : Prop :=
  match t with
  | tvar x => (x < n)%nat
  | tunit => True
  | tbool _ => True
  | tint _ => True
  | tfloat _ => True
  | tstring _ => True
  | tabs T t' => closed (S n) t'
  | tapp t1 t2 => closed n t1 /\ closed n t2
  | tTabs t' => closed n t'
  | tTapp t' T => closed n t'
  | tlet t1 t2 => closed n t1 /\ closed (S n) t2
  | tpair t1 t2 => closed n t1 /\ closed n t2
  | tfst t' => closed n t'
  | tsnd t' => closed n t'
  | tinl T t' => closed n t'
  | tinr T t' => closed n t'
  | tcase t' t1 t2 => closed n t' /\ closed (S n) t1 /\ closed (S n) t2
  | tfold T t' => closed n t'
  | tunfold t' => closed n t'
  | tresource _ _ _ => True
  | tresadd t1 t2 => closed n t1 /\ closed n t2
  | tresmul t1 t2 => closed n t1 /\ closed n t2
  | tresdiv t1 t2 => closed n t1 /\ closed n t2
  | tadaptive C objs sols => True  (** TODO: refine *)
  | thandle t' handlers ret => closed n t' /\ closed n ret  (** TODO: refine handler cases *)
  end.

(** Values are closed terms in normal form *)
Inductive value : tm -> Prop :=
  | v_unit : value tunit
  | v_bool : forall b, value (tbool b)
  | v_int : forall n, value (tint n)
  | v_float : forall r, value (tfloat r)
  | v_string : forall s, value (tstring s)
  | v_abs : forall T t, closed 1 t -> value (tabs T t)
  | v_Tabs : forall t, closed 0 t -> value (tTabs t)
  | v_pair : forall v1 v2, value v1 -> value v2 -> value (tpair v1 v2)
  | v_inl : forall T v, value v -> value (tinl T v)
  | v_inr : forall T v, value v -> value (tinr T v)
  | v_fold : forall T v, value v -> value (tfold T v)
  | v_resource : forall q rk d, value (tresource q rk d).

(** * Notations *)

Declare Scope type_scope.
Delimit Scope type_scope with type.

(** Convenient notation for function types *)
Notation "T1 '→' T2" := (TArr T1 T2) (at level 99, right associativity) : type_scope.

(** Convenient notation for product types *)
Notation "T1 '×' T2" := (TProd T1 T2) (at level 40, left associativity) : type_scope.

(** Note: No notation for sum types to avoid conflict with + *)
(** Use TSum T1 T2 directly *)
