Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.ReductionInvariance.

Require Import Arith.
Require Import Coq.Logic.Decidable.


Lemma msubst_IWrap : forall ss F T M t',
    msubst_term ss (IWrap F T M) t' ->
    exists M', msubst_term ss M M' /\ t' = IWrap F T M'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists M. split. constructor. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    rename t0' into M'.
    eapply IHss in H5.
    destruct H5 as [M'' [H0 H1]].
    subst.
    exists M''.
    split.
    + eapply msubst_term__cons; eauto.
    + reflexivity.
Qed.

Lemma msubstA_IWrap : forall ss F T M t',
    msubstA ss (IWrap F T M) t' ->
    exists M', msubstA ss M M' /\ t' = IWrap (msubstT ss F) (msubstT ss T) M'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists M. split. constructor. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    rename t0' into M'.
    eapply IHss in H5.
    destruct H5 as [M'' [H0 H1]].
    subst.
    exists M''.
    split.
    + eapply msubstA_cons; eauto.
    + reflexivity.
Qed.

Lemma inspect_eval__IWrap_1 : forall F T e j e_f,
    IWrap F T e =[j]=> e_f ->
    exists j1 e_f1, e =[j1]=> e_f1 /\ j1 <= j.
Proof.
  intros.
  inversion H. subst.
  exists j, v0. 
  split; eauto.
Qed.

Lemma inspect_eval__IWrap_2 : forall F T e j e_f j_1 v_f1,
    IWrap F T e =[j]=> e_f ->
    terminates_incl e j_1 v_f1 j ->
    j - j_1 = 0 /\ j = j_1 /\ e_f = IWrap F T v_f1.
Proof.
  intros.
  inversion H. subst.
  destruct H0.
  assert (v0 = v_f1 /\ j = j_1) by (eapply eval__deterministic; eauto).
  destruct H2. subst.
  split.
  - apply Nat.sub_diag.
  - auto.
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

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    eapply T_IWrap; eauto.
  }

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    eapply T_IWrap; eauto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  destruct (msubstA_IWrap _ _ _ _ _ HmsA__e_msa) as [eb_sa [HmsA__eb_msa Heq]].
  destruct (msubstA_IWrap _ _ _ _ _ HmsA__e'_msa) as [eb'_sa [HmsA__eb'_msa Heq']].
  subst.
  destruct (msubst_IWrap _ _ _ _ _ Hms__e_ms) as [eb_s [Hms__eb_ms Heq]].
  destruct (msubst_IWrap _ _ _ _ _ Hms__e'_ms) as [eb'_s [Hms__eb'_ms Heq']].
  subst.

  autorewrite with RC.

  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR.
      eapply T_IWrap; eauto.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR. destruct H0.
      eapply T_IWrap; eauto.
    - rewrite mupd_empty; eauto.
  }
  
  (** 
      Consider arbitrary j, ef such that 
      # j < k,
      # IWrap F T e -[j]-> e_f, and
      # irred(e_f)
  *)
  intros j Hlt__j e_f ev__e.

  (** 
      Hence, by inspection of the operational semantics, it follows that there
      exist j_1 and e_f1 such that
      # e =[j_1]=> e_f1, 
      # irred(e_f1) and
      # j_1 <= j
  *)
  assert (temp: exists j_1 e_f1, eb_s =[j_1]=> e_f1 /\ j_1 <= j) by eauto using inspect_eval__IWrap_1.
  destruct temp as [j_1 [e_f1 [Hev__e Hle__j_1]]].

  (** 
      Instantiate the second conjunct of H_RC with k. ... Instantiate this with 
      j_1, e_f1. Note that
      # j_1 < k, which follows from j_1 <= j < k,
      # e =[j_1]=> e_f1, and
      # irred(e_f1)
  *)
  assert (Hlt__j_1 : j_1 < k) by eauto using Nat.le_lt_trans. 

  unfold LR_logically_approximate in IH_LR.
  destruct IH_LR as [H20 [H21 IH_LR]].
  assert (H_RC: RC k S rho eb_s eb'_s) by eauto.
  remember H_RC as H_RC'. clear HeqH_RC'.
  autorewrite with RC in H_RC.
  destruct H_RC as [H22 [H23 H_RC]].
  remember (H_RC j_1 Hlt__j_1 e_f1 Hev__e) as temp.
  clear Heqtemp. clear H_RC. rename temp into H_RC.

  (** 
      Hence, there exists e'_f1 (and j'_1) such that
      # e' =[j'_1]=> e'_f1, and
      # (k - j_1, e_f1, e'_f1) \in RV[[beta_reduce (unwrapIFix F K T)]]
  *)
  destruct H_RC as [e'_f1 [j'_1 [Hev__e1' H_RC]]].
  assert (H_RV: RC (k - j_1) S rho e_f1 e'_f1). {
    eapply RC_monotone.
    - eapply eval_preserves_R; eauto.
      split.
      + eauto.
      + eauto.
    - apply helper2. assumption.
  }
  clear H_RC.

  (**
      Hence, 
        e_f1 `equiv` v_f1, and
        e'_f1 `equiv` v'_f1.
  *)
  rename e_f1 into v_f1.
  rename e'_f1 into v'_f1.

  (**
      Note that
        IWrap F T e -[j_1]->
        IWrap F T e_f1 =
        IWrap F T v_f1 -[j-j_1]->
        e_f

        Since IWrap F T v_f1 is a value, we have irred(IWrap F T v_f1).
        Hence, j - j_1 = 0 (and j = j_1) and e_f `equiv` IWrap F T v_f1.
  *)
  assert (temp: j - j_1 = 0 /\ j = j_1 /\ e_f = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_f1). {
    eapply inspect_eval__IWrap_2; eauto. split; auto.
  }
  destruct temp as [Heq1 [Heq2 Heq3]].

  (**
      Let e'_f = IWrap F T v'_f1 (and j' = j'_1)
  *)
  exists (IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_f1). exists j'_1.
  
  (** messy below *)
  split. {
    eapply E_IWrap; eauto.
  }

  intros v v' Heq4 Heq5 i Hlt__i K0 S' Hkind_K0 Hnorm'.
  subst. inversion Heq4. subst.
  inversion Heq5. subst.

  assert (K = K0) by apply skip. (* TODO *)
  subst.
  assert (S = S') by apply skip. (* TODO *)
  subst.

  eapply RC_monotone.
  + eapply H_RV. 
  + apply helper4.
    assumption.
Qed.