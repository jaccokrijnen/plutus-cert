Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.SubstituteTCA.


Lemma normalisation_preserves_kinding : forall Delta T T' K,
    Delta |-* T : K ->
    normalise T T' ->
    Delta |-* T' : K.
Proof.
  intros.
  generalize dependent T'.
  induction H; intros T' Hnorm; try solve [inversion Hnorm; subst; eauto with typing].
  - inversion Hnorm.
    + subst.
      inversion H. subst.
      eapply substituteTCA_preserves_kinding; eauto.
      apply skip. (* TODO *)
    + subst.
      eauto with typing.
Qed.