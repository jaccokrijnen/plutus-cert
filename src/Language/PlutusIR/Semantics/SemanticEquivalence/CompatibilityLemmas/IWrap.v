Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.

Lemma msubst_IWrap : forall ss F T M,
    msubst_term ss (IWrap F T M) = IWrap F T (msubst_term ss M).
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma msubstA_IWrap : forall ss F T M,
    msubstA_term ss (IWrap F T M) = IWrap (msubstT ss F) (msubstT ss T) (msubstA_term ss M).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma helper1 : forall k j,
    j < k ->
    0 < k.
Proof.
  intros.
  inversion H.
  - apply Nat.lt_0_succ.
  - apply Nat.lt_0_succ.
Qed.

Lemma helper2 : forall k j,
  j < k ->
  k - j <= k.
Proof.
  induction 1.
  - rewrite <- minus_Sn_m; auto.
    rewrite Nat.sub_diag.
    rewrite <- Nat.succ_le_mono.
    apply Nat.le_0_l.
  - rewrite <- minus_Sn_m; auto.
    + rewrite <- Nat.succ_le_mono.
      assumption.
    + inversion H; subst.
      * apply le_S. apply le_n.
      * apply le_S.
        rewrite Nat.succ_le_mono.
        assumption.
Qed.  

Lemma helper3 : forall k j,
  j < k ->
  0 < k - j.
Proof.
  induction 1.
  - rewrite <- minus_Sn_m; auto.
    rewrite Nat.sub_diag.
    apply Nat.lt_0_succ.
  - rewrite <- minus_Sn_m; auto.
    inversion H; subst.
    + apply le_S.
      apply le_n.
    + apply le_S.
      rewrite Nat.succ_le_mono.
      assumption.
Qed.

Lemma helper4 : forall i k j,
  i < k - j ->
  i <= k - j.
Proof.
  intros.
  induction H.
  - apply le_S.
    apply le_n.
  - apply le_S.
    assumption.
Qed.

Lemma compatibility_IWrap : forall Delta Gamma F T e e' K S,
    Delta |-* T : K ->
    Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
    normalise (unwrapIFix F K T) S ->
    LR_logically_approximate Delta Gamma e e' S ->
    LR_logically_approximate Delta Gamma (IWrap F T e) (IWrap F T e') (Ty_IFix F T).
Proof.
  intros Delta Gamma F T e e' K S Hkind__T Hkind__F Hnorm IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

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
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      eauto with typing.
    - rewrite mupd_empty; eauto.
  }

  rewrite msubstA_IWrap. rewrite msubstA_IWrap.
  rewrite msubst_IWrap. rewrite msubst_IWrap.
  
  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f.
  subst.

  rename v0 into e_f. 

  assert (HRC : 
    RC k S rho 
      (msubst_term env (msubstA_term (msyn1 rho) e)) 
      (msubst_term env' (msubstA_term (msyn2 rho) e'))
  ) by eauto. 

  eapply RC_to_RV in HRC as temp; eauto.
  destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

  eexists. eexists.
  split. eapply E_IWrap. eauto.

  eexists. eexists.
  split. reflexivity.
  split. reflexivity.

  intros.

  assert (K0 = K) by apply skip. (* TODO *)
  subst.
  assert (S0 = S) by apply skip. (* TODO *)
  subst.

  eapply RV_to_RC.

  eapply RV_monotone.
  + eapply HRV. 
  + apply helper4.
    assumption.
Qed.