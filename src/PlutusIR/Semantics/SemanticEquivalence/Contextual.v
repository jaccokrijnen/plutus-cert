From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Semantics.Static.Typing.Typing.
From PlutusCert Require Import PlutusIR.Semantics.Dynamic.Bigstep.
From PlutusCert Require Import SemanticEquivalence.Validator.
From PlutusCert Require Import SemanticEquivalence.Congruence.
From PlutusCert Require Import Util.Tactics.

Require Import Lists.List.
Import ListNotations.

Definition eval' t v := exists j, eval t v j.

Definition contextually_approximate
  (e e' : term) Δ Γ T
  :=
  (Δ ,, Γ |-+ e  : T) /\
  (Δ ,, Γ |-+ e' : T) /\
  forall (C : context),
    ([] ,, [] |- C : (Δ, Γ, T) ↪ ty_unit) ->
      (context_fill C e ==> val_unit -> context_fill C e' ==> val_unit) /\
      (context_fill C e ==>e -> context_fill C e' ==>e )
.

Notation "Δ ',,' Γ '|-' e1 ≤-ctx e2 ':' T" := (contextually_approximate e1 e2 Δ Γ T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

Definition contextually_equivalent
  Δ Γ (e e' : term) T
  :=
  (Δ ,, Γ |-+ e  : T) /\
  (Δ ,, Γ |-+ e' : T) /\
  forall (C : context),
    ([] ,, [] |- C : (Δ, Γ, T) ↪ ty_unit) ->
      (context_fill C e ==> val_unit <-> context_fill C e' ==> val_unit) /\
      (context_fill C e ==>e <-> context_fill C e' ==>e )
.

Notation "Δ ',,' Γ '|-' e1 =ctx e2 ':' T" := (contextually_equivalent Δ Γ e1 e2 T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

(* Alternative formulation of contextual equivalence *)
Lemma approx_equiv Δ Γ e e' T :
  (Δ ,, Γ |- e ≤-ctx e' : T ) /\ (Δ ,, Γ |- e'≤-ctx e  : T) <-> (Δ ,, Γ |- e =ctx e' : T )
  .
Admitted.


Lemma ctx_instantiate Δ Γ s t T C :
  Δ ,, Γ |- s =ctx t : T ->
  ([] ,, [] |- C : (Δ, Γ, T) ↪ ty_unit) ->
    (context_fill C s ==> val_unit <-> context_fill C t ==> val_unit) /\
    (context_fill C s ==>e <-> context_fill C t ==>e)
.
Proof.
Admitted.

Lemma type_respecting_l Δ Γ s t T :
  Δ ,, Γ |- s =ctx t : T ->
  Δ ,, Γ |-+ s : T.
Proof.
  unfold contextually_equivalent, contextually_approximate.
  intros H.
  destruct_hypos.
  assumption.
Qed.

Lemma type_respecting_r Δ Γ s t T :
  Δ ,, Γ |- s =ctx t : T ->
  Δ ,, Γ |-+ t : T.
Proof.
  unfold contextually_equivalent, contextually_approximate.
  intros H.
  destruct_hypos.
  assumption.
Qed.

Lemma ctx_consistent s t :
  ([] ,, [] |- s =ctx t : ty_validator) ->
  s =val t
.
Proof.
  intros H_ctx.
  unfold validator_equivalent.
  split; eauto using type_respecting_l.
  split; eauto using type_respecting_r.
  intros d i H_i.
  apply ctx_instantiate with (C := C_Apply_L C_Hole i) in H_ctx.
  simpl in H_ctx.
  - assumption.
  - (* C is well-typed *)
    unfold ty_unit.
    subst i.
    eauto using context_has_type, has_type.
Qed.

Section contextually_approximate_lemmas.

  Lemma contextually_approximate_reflexive : forall Δ Γ e T,
  Δ ,, Γ |-+ e : T ->
  Δ ,, Γ |- e ≤-ctx e : T.
  Proof.
    unfold contextually_approximate.
    intros.
    repeat split; auto.
  Qed.

  Lemma contextually_approximate_transitive : forall Δ Γ e1 e2 e3 T,
    Δ ,, Γ |- e1 ≤-ctx e2 : T ->
    Δ ,, Γ |- e2 ≤-ctx e3 : T ->
    Δ ,, Γ |- e1 ≤-ctx e3 : T.
  Proof with eauto.
    unfold contextually_approximate.
    intros.
    repeat (match goal with | H : ?x /\ ?y |- _ => destruct H end).
    intuition.
  Qed.

  Lemma contextually_approximate_antisymmetric : forall Δ Γ e1 e2 T,
    Δ ,, Γ |- e1 ≤-ctx e2 : T ->
    Δ ,, Γ |- e2 ≤-ctx e1 : T ->
    Δ ,, Γ |- e1 =ctx e2 : T.
  Proof.
    setoid_rewrite <- approx_equiv.
    unfold contextually_equivalent.
    eauto.
  Qed.

  Notation "≤-ctx-refl" := (contextually_approximate_reflexive).
  Notation "≤-ctx-trans" := (contextually_approximate_transitive).
  Notation "≤-ctx-antisym" := (contextually_approximate_antisymmetric).

End contextually_approximate_lemmas.

Section contextually_equivalent_props.

  Lemma contextually_equivalent_reflexive : forall Δ Γ e T,
  Δ ,, Γ |-+ e : T ->
  Δ ,, Γ |- e =ctx e : T.
  Proof.
    setoid_rewrite <- approx_equiv.
    unfold contextually_equivalent.
    auto using contextually_approximate_reflexive.
  Qed.

  Lemma contextually_equivalent_transitive : forall Δ Γ e1 e2 e3 T,
    Δ ,, Γ |- e1 =ctx e2 : T ->
    Δ ,, Γ |- e2 =ctx e3 : T ->
    Δ ,, Γ |- e1 =ctx e3 : T.
  Proof.
    unfold contextually_equivalent.
    intuition; eauto using contextually_approximate_transitive.
  Qed.

  Lemma contextually_equivalent_symmetric : forall Δ Γ e1 e2 T,
    Δ ,, Γ |- e1 =ctx e2 : T ->
    Δ ,, Γ |- e2 =ctx e1 : T.
  Proof.
    unfold contextually_equivalent.
    intuition.
  Qed.


  Notation "=ctx-refl" := (contextually_equivalent_reflexive).
  Notation "=ctx-trans" := (contextually_equivalent_transitive).
  Notation "=ctx-sym" := (contextually_equivalent_symmetric).


  (* ad-hoc tactic for solving typing *)
  Ltac solve_typing := try (solve [eauto using context_has_type__fill, type_respecting_l, type_respecting_r]).

  Lemma ctx_compatible : context_compatible contextually_equivalent.
  Proof with solve_typing.
    intros Δ Γ s t T.
    intros H_equiv.
    intros C Δ1 Γ1 T1 H_ty_C.
    unfold contextually_equivalent.
    split...
    split...
    intros C0 H_ty_C0.
    split;
      setoid_rewrite <- context_comp_fill;
      eapply H_equiv;
      eauto using context_comp__has_type.
  Qed.

End contextually_equivalent_props.
