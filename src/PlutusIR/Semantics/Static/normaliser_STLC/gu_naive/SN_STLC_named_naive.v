From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.
From PlutusCert Require Import alpha alpha_rename rename util alpha_ctx_sub freshness alpha_freshness alpha_step step alpha_sub.

(* TODO: Used to be Prop. Ask Jacco*)
Inductive step_naive : term -> term -> Set :=
| step_beta (x : string) (A : type) (s t : term) :
    step_naive (tmapp (tmlam x A s) t) ( substituteT x t s)
| step_appL s1 s2 t :
    step_naive s1 s2 -> step_naive (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step_naive t1 t2 -> step_naive (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step_naive s1 s2 -> step_naive (tmlam x A s1) (tmlam x A s2).

Definition to_unique_binders (s : term) := s.

Lemma to_unique_binders_alpha s : Alpha [] s (to_unique_binders s).
Admitted.

Inductive GU_vars : term -> Set :=
| GU_var x : GU_vars (tmvar x)
(* in app, if s and t do not share GU_vars: *)
| GU_app s t : 
    GU_vars s -> 
    GU_vars t -> 
    (* Intersection of bound type variables of s and t is empty *)
    forall (H_btv_btv_empty : forall x, In x (btv t) -> ~ In x (btv s)),
    (* Intersection of bound type variables of s and free type variables of t is empty *)
    forall (H_btv_ftv_empty : forall x, In x (btv s) -> ~ In x (ftv t)),
    (* Intersection of free type variables of s and bound type variables of t is empty *)
    forall (H_ftv_btv_empty : forall x, In x (btv t) -> ~ In x (ftv s)),
    GU_vars (tmapp s t)
| GU_lam x A s : 
    GU_vars s -> 
    ~ In x (btv s) ->
    GU_vars (tmlam x A s).

Lemma to_unique_binders_unique s : GU_vars (to_unique_binders s).
Admitted.

(* Examples
λ x. x is GU_vars
λ x. y is GU_vars
λ x. λ y. x is GU_vars

(λ x. x) y is GU_vars
(λ x. x) x is not GU_vars (* free var is equal to a bound var*)
(λ y. x) x is GU_vars (* all vars with the same name refer to the same term*)
*)

(* If a term has globally unique binders, then it has unique binders*)

Inductive step_gu_naive : term -> term -> Set :=
| step_gu_naive_intro s t : 
    step_naive (to_unique_binders s) t ->
    step_gu_naive s t.

(* used to be prop (TODO: Defined also in SN_STCL_named )*)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Notation SN_na := (@sn step_gu_naive).

(* If we have substituteT X U s, we need some assumption that U and s already have unique bindrs*)

Lemma step_gu_naive_subst s t U X : 
  step_gu_naive s t -> 
  {α : term & 
  (step_gu_naive (substituteT X U s) α) * (nil ⊢ α ~ (substituteT X U t))} .
Proof.
    intros.
    inversion H; subst.
    (* ok... we need some guarantees that free vars are not changed by to_unique_binders*)

Admitted.


Theorem SN_naive E s T : has_type E s T -> {s' & nil ⊢ s ~ s' * SN_na s'}.
Admitted.