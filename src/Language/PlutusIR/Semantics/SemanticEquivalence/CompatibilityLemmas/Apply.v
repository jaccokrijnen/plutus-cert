Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.

Lemma helper : forall n j k,
    j + n < k ->
    j < k.
Proof.
  induction n; intros.
  - rewrite <- plus_n_O in H.
    assumption.
  - rewrite <- plus_n_Sm in H.
    induction H.
    + subst. eauto.
    + subst. eauto.
Qed.

Lemma msubst_Apply : forall ss t1 t2,
    msubst_term ss (Apply t1 t2) = Apply (msubst_term ss t1) (msubst_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Apply : forall ss t1 t2,
    msubstA_term ss (Apply t1 t2) = Apply (msubstA_term ss t1) (msubstA_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma compatibility_Apply : forall Delta Gamma e1 e2 e1' e2' T1 T2 ,
    LR_logically_approximate Delta Gamma e1 e1' (Ty_Fun T1 T2) ->
    LR_logically_approximate Delta Gamma e2 e2' T1 ->
    LR_logically_approximate Delta Gamma (Apply e1 e2) (Apply e1' e2') T2.
Proof.
  intros Delta Gamma e1 e2 e1' e2' T1 T2 IH_LR1 IH_LR2.
  unfold LR_logically_approximate.

  destruct IH_LR1 as [Htyp__e1 [Htyp__e1' IH1]].
  destruct IH_LR2 as [Htyp__e2 [Htyp__e2' IH2]].


  split. eauto with typing.
  split. eauto with typing. 

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }

  rewrite msubstA_Apply. rewrite msubstA_Apply. 
  rewrite msubst_Apply. rewrite msubst_Apply.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f; subst.
  - rename v2 into e_f2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j0 into j_3.

    assert (HRC1 : 
      RC k (Ty_Fun T1 T2) rho 
        (msubst_term env (msubstA_term (msyn1 rho) e1)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e1'))
    ) by eauto.

    assert (Hlt__j_1 : j_1 < k) by eauto using helper.
    eapply RC_to_RV in HRC1 as temp; eauto.
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].
    clear Hlt__j_1.

    assert (k - j_1 <= k) by apply skip.
    assert (HRC2 : 
      RC (k - j_1) T1 rho 
        (msubst_term env (msubstA_term (msyn1 rho) e2)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e2'))
    ) by eauto using RG_monotone.
    clear H.

    assert (Hlt__j_2 : j_2 < k - j_1). {
      apply skip.
    }
    eapply RC_to_RV in HRC2 as temp; eauto.
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].
    clear Hlt__j_2.

    assert (Hlt__0 : 0 < k - j_1) by apply skip.
    eapply RV_functional_extensionality in HRV1 as temp; eauto.
    destruct temp as [x0 [e_body [ x0' [e'_body [Heq [Heq' Hfe]]]]]].
    clear Hlt__0.
    inversion Heq. subst. clear Heq.

    assert (k - j_1 - j_2 - 1 <= k - j_1 - j_2) by apply skip.
    eapply RV_monotone in HRV2; eauto.
    clear H.

    assert (k - j_1 - j_2 - 1 < k - j_1) by apply skip.
    eapply Hfe in H as HRC0; eauto.
    clear H.

    assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3) by apply skip.
    rewrite H.
    clear H.

    assert (j_3 < k - j_1 - j_2 - 1) by apply skip.
    eapply RC_to_RV in HRC0 as temp; eauto.
    clear H.
    destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

    eexists. eexists. 
    split. 
    + eapply E_Apply. all: eauto.
    + eapply RV_condition; eauto.
      apply skip.
Admitted.