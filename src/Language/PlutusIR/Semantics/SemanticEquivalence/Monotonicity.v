Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

Require Import Arith.

Lemma e2 : forall j j0 k j1,
    j <= k ->
    j0 < j - j1 ->
    j0 < k - j1.
Proof. Admitted.

Lemma R_monotone : forall k T v1 v2 j,
  True ->
  True ->
  j <= k ->
  R k T v1 v2 ->
  R j T v1 v2.
Proof.
  destruct T.
  - intros.
    apply R_impossible_type in H2.
    destruct H2.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply e2 with j; auto.
    + eassumption.
    + eassumption.
    + eassumption.
    + assumption.
    + assumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply e2 with j; auto.
    + assumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
    destruct H7.
    destruct H7.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H8.
    + apply e2 with j; auto.
    + eassumption.
    + eassumption.
    + eassumption.
  - intros.
    autorewrite with R in H2.
    autorewrite with R.
    destruct H2.
    destruct H3.
    split; auto.
    split; auto.
    intros.
    assert (j1 < k). {
      eapply le_trans; eauto.
    }

    edestruct H4; eauto.
  - intros.
    apply R_impossible_type in H2.
    destruct H2.
  - intros.
    apply R_impossible_type in H2.
    destruct H2.
Qed.