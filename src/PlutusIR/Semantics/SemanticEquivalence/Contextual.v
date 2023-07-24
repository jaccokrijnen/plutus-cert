From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Semantics.Static.Typing.
From PlutusCert Require Import PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lists.List.
Import ListNotations.

Import NamedTerm.

Definition contextually_approximate
  (e e' : Term) Δ Γ T
  :=
  (Δ ,, Γ |-+ e  : T) /\
  (Δ ,, Γ |-+ e' : T) /\
  forall (C : Context) T₁,
    ([] ,, [] |-C C : (Δ ,, Γ ▷ T) ↝ T₁) ->
    context_apply C e  ⇓ ->
    context_apply C e' ⇓.

Notation "Δ ',,' Γ '|-' e1 ⪯-ctx e2 ':' T" := (contextually_approximate e1 e2 Δ Γ T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

Definition contextually_equivalent
  (e e' : Term) Δ Γ T
  :=
  (Δ ,, Γ |- e ⪯-ctx e' : T )
  /\ (Δ ,, Γ |- e'⪯-ctx e  : T)
  .

Notation "Δ ',,' Γ '|-' e1 ≃-ctx e2 ':' T" := (contextually_equivalent e1 e2 Δ Γ T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).


Definition ciu_equivalent e e' T :=
  ([],, [] |-+ e  : T)  /\
  ([],, [] |-+ e' : T) /\
  ((e ⇓) <-> (e' ⇓)).

Notation "|- e1 ≃-ciu e2 ':' T" := (ciu_equivalent e1 e2 T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).

Section contextually_approximate_lemmas.

  Lemma contextually_approximate_reflexive : forall Δ Γ e T,
  Δ ,, Γ |-+ e : T ->
  Δ ,, Γ |- e ⪯-ctx e : T.
  Proof.
    unfold contextually_approximate.
    auto.
  Qed.

  Lemma contextually_approximate_transitive : forall Δ Γ e1 e2 e3 T,
    Δ ,, Γ |- e1 ⪯-ctx e2 : T ->
    Δ ,, Γ |- e2 ⪯-ctx e3 : T ->
    Δ ,, Γ |- e1 ⪯-ctx e3 : T.
  Proof.
    unfold contextually_approximate.
    intros.
    repeat (match goal with | H : ?x /\ ?y |- _ => destruct H end).
    eauto.
  Qed.

  Lemma contextually_approximate_antisymmetric : forall Δ Γ e1 e2 T,
    Δ ,, Γ |- e1 ⪯-ctx e2 : T ->
    Δ ,, Γ |- e2 ⪯-ctx e1 : T ->
    Δ ,, Γ |- e1 ≃-ctx e2 : T.
  Proof.
    unfold contextually_equivalent.
    eauto.
  Qed.

  Notation "⪯-ctx-refl" := (contextually_approximate_reflexive).
  Notation "⪯-ctx-trans" := (contextually_approximate_transitive).
  Notation "⪯-ctx-antisym" := (contextually_approximate_antisymmetric).

End contextually_approximate_lemmas.

Section contextually_equivalent_props.

  Lemma contextually_equivalent_reflexive : forall Δ Γ e T,
  Δ ,, Γ |-+ e : T ->
  Δ ,, Γ |- e ≃-ctx e : T.
  Proof.
    unfold contextually_equivalent.
    auto using contextually_approximate_reflexive.
  Qed.

  Lemma contextually_equivalent_transitive : forall Δ Γ e1 e2 e3 T,
    Δ ,, Γ |- e1 ≃-ctx e2 : T ->
    Δ ,, Γ |- e2 ≃-ctx e3 : T ->
    Δ ,, Γ |- e1 ≃-ctx e3 : T.
  Proof.
    unfold contextually_equivalent.
    intros.
    unfold contextually_approximate in *.
    repeat (match goal with | H : ?x /\ ?y |- _ => destruct H end).
    repeat (match goal with |- ?x /\ ?y => split end).
    all: eauto.
  Qed.

  Lemma contextually_equivalent_symmetric : forall Δ Γ e1 e2 T,
    Δ ,, Γ |- e1 ≃-ctx e2 : T ->
    Δ ,, Γ |- e2 ≃-ctx e1 : T.
  Proof.
    unfold contextually_equivalent.
    intros.
    repeat (match goal with | H : ?x /\ ?y |- _ => destruct H end).
    repeat (match goal with |- ?x /\ ?y => split end).
    all: eauto.
  Qed.


  Notation "≃-ctx-refl" := (contextually_equivalent_reflexive).
  Notation "≃-ctx-trans" := (contextually_equivalent_transitive).
  Notation "≃-ctx-sym" := (contextually_equivalent_symmetric).

End contextually_equivalent_props.
