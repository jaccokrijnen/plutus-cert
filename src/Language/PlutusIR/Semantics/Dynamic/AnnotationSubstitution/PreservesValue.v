Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.



Theorem substituteA_preserves_value : forall v v' a T,
    value v ->
    substituteA a T v v' ->
    value v'.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0; subst; auto]. 
Admitted.

Theorem msubstA_preserves_value : forall envA v v',
    value v ->
    msubstA envA v v' ->
    value v'.
Proof.
  induction envA.
  - intros.
    inversion H0.
    subst.
    assumption.
  - intros.
    inversion H0.
    subst.
    eapply IHenvA.
    + eapply substituteA_preserves_value; eauto.
    + eauto.
Qed. 

