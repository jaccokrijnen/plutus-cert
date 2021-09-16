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

Lemma RC_monotone : forall k T j v v',
    value v ->
    value v' ->
    RC (S k) T v v' ->  
    j <= (S k) ->
    RC j T v v'.
Proof.
  intros k T j v v' Hval_v Hval_v' RC Hlt.

  assert (Hterm : terminates_excl v 0 v (S k)). {
    split.
    - eapply eval_value. assumption. 
    - apply Nat.lt_0_succ.
  }


  destruct T.
  - eapply RC_impossible_type in RC; eauto.
    destruct RC.
  - autorewrite with RC in RC.
    autorewrite with RC.
    destruct RC.
    destruct H0.
    split; auto.
    split; auto.
    intros j0 Hlt_j0 e_f0 Hev__e_f0.
    assert (j0 < S k). {
      eapply le_trans; eauto.
    }

    edestruct H1; eauto.
    destruct H3.
    destruct H3.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H4.
    + eassumption.
    + eassumption.
    + apply e2 with j; auto.
    + eassumption.
    + eassumption.
    + eassumption.
  - autorewrite with RC in RC.
    autorewrite with RC.
    destruct RC.
    destruct H0.
    split; auto.
    split; auto.
    intros j0 Hlt_j0 e_f0 Hev__e_f0.
    assert (j0 < S k). {
      eapply le_trans; eauto.
    }

    edestruct H1; eauto.
    destruct H3.
    destruct H3.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H4.
    + assumption.
    + assumption.
    + apply e2 with j; auto.
    + assumption.
  - autorewrite with RC in RC.
    autorewrite with RC.
    destruct RC.
    destruct H0.
    split; auto.
    split; auto.
    intros j0 Hlt_j0 e_f0 Hev__e_f0.
    assert (j0 < S k). {
      eapply le_trans; eauto.
    }

    edestruct H1; eauto.
    destruct H3.
    destruct H3.
    exists x.
    exists x0.
    split; auto.

    intros.
    eapply H4.
    + assumption.
    + assumption.
    + apply e2 with j; auto.
  - autorewrite with RC in RC.
    autorewrite with RC.
    destruct RC.
    destruct H0.
    split; auto.
    split; auto.
    intros j0 Hlt_j0 e_f0 Hev__e_f0.
    assert (j0 < S k). {
      eapply le_trans; eauto.
    }

    edestruct H1; eauto.
  - eapply RC_impossible_type in RC; eauto.
    destruct RC.
  - eapply RC_impossible_type in RC; eauto.
    destruct RC.
Qed.