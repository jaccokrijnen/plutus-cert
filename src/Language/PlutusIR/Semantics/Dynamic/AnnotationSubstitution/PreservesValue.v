Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.



Theorem substituteA_preserves_value : forall v a T,
    value v ->
    value <{ [[T / a] v }>.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0; subst; auto]. 
Admitted.

Theorem msubstA_preserves_value : forall envA v,
    value v ->
    value (msubstA_term envA v).
Proof.
  induction envA.
  - intros.
    simpl.
    assumption.
  - intros.
    simpl.
    destruct a.
    eapply IHenvA.
    eapply substituteA_preserves_value; eauto.
Qed. 

