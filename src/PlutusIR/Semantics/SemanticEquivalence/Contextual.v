From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Semantics.Static.Typing.
From PlutusCert Require Import PlutusIR.Semantics.Dynamic.Bigstep.
From PlutusCert Require Import SemanticEquivalence.Validator.
From PlutusCert Require Import Util.Tactics.

Require Import Lists.List.
Import ListNotations.



Definition ty_unit : ty :=
  Ty_Builtin DefaultUniUnit.

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
  (e e' : term) Δ Γ T
  :=
  (Δ ,, Γ |- e ≤-ctx e' : T )
  /\ (Δ ,, Γ |- e'≤-ctx e  : T)
  .

Notation "Δ ',,' Γ '|-' e1 =ctx e2 ':' T" := (contextually_equivalent e1 e2 Δ Γ T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

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

End contextually_equivalent_props.
