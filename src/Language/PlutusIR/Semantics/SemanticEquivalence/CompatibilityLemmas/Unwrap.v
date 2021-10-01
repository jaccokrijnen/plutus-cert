Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.ReductionInvariance.

Require Import Arith.
Require Import Coq.Logic.Decidable.

Lemma msubst_Unwrap : forall ss M t',
    msubst_term ss (Unwrap M) t' ->
    exists M', msubst_term ss M M' /\ t' = Unwrap M'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists M. split. constructor. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    rename t0' into M'.
    eapply IHss in H5.
    destruct H5 as [M'' [H0 H3]].
    subst.
    exists M''.
    split.
    + eapply msubst_term__cons; eauto.
    + reflexivity.
Qed.

Lemma msubstA_Unwrap : forall ss M t',
    msubstA ss (Unwrap M) t' ->
    exists M', msubstA ss M M' /\ t' = Unwrap M'.
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
  

Lemma inspect_eval__Unwrap_1 : forall e j e_f,
    Unwrap e =[j]=> e_f ->
    exists j_1 e_f1, e =[j_1]=> e_f1 /\ j_1 <= j.
Proof.
  intros.
  inversion H. subst.
  exists k0, (IWrap F T e_f). 
  split; eauto.
  rewrite plus_comm.
  apply le_S.
  apply le_n.
Qed.

Lemma helper0 : forall j,
  j + 1 - j - 1 = 0.
Proof. induction j; auto. Qed.

Lemma inspect_eval__Unwrap_2 : forall e j e_f j_1 F T v_f11,
    Unwrap e =[j]=> e_f ->
    terminates_incl e j_1 (IWrap F T v_f11) j ->
    j - j_1 - 1 = 0 /\ j = j_1 + 1 /\ e_f = v_f11.
Proof.
  intros.
  inversion H. subst.
  destruct H0.
  assert (IWrap F0 T0 e_f = IWrap F T v_f11 /\ k0 = j_1) 
    by (eapply eval__deterministic; eauto).
  destruct H3. subst.
  inversion H3. subst.
  split; eauto using helper0.
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

Lemma helper3 : forall k j j_1,
    j = j_1 + 1 ->
    j_1 < k ->
    k - j < k - j_1.
Proof. Admitted.

Lemma helper4 : forall k j,
    j < k ->
    0 < (k - j).
Proof. Admitted.

Lemma compatibility_Unwrap : forall Delta Gamma F T e e' K S,
    Delta |-* T : K ->
    normalise (unwrapIFix F K T) S ->
    LR_logically_approximate Delta Gamma e e' (Ty_IFix F T)->
    LR_logically_approximate Delta Gamma (Unwrap e) (Unwrap e') S.
Proof.
  intros Delta Gamma F T e e' K S Hkind__T Hnorm IH_LR.
  unfold LR_logically_approximate.

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    eapply T_Unwrap; eauto.
  }

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    eapply T_Unwrap; eauto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  destruct (msubstA_Unwrap _ _ _ HmsA__e_msa) as [eb_msa [HmsA__eb_msa Heq]].
  destruct (msubstA_Unwrap _ _ _ HmsA__e'_msa) as [eb'_msa [HmsA__eb'_msa Heq']].
  subst.

  destruct (msubst_Unwrap _ _ _ Hms__e_ms) as [eb_ms [Hms__eb_ms Heq]].
  destruct (msubst_Unwrap _ _ _ Hms__e'_ms) as [eb'_ms [Hms__eb'_ms Heq']].
  subst.

  autorewrite with RC.

  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply T_Unwrap.
      + apply skip.
      + apply skip.
      + apply skip.
    - rewrite mupd_empty. reflexivity.
  } 
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply T_Unwrap.
      all: apply skip.
    - rewrite mupd_empty. reflexivity.
  } 

  (* Second part of the proof *)

  (** 
      Consider arbitrary j, ef such that 
      # j < k,
      # Unwrap e -[j]-> e_f, and
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
  assert (temp: exists j_1 e_f1, eb_ms =[j_1]=> e_f1 /\ j_1 <= j) by eauto using inspect_eval__Unwrap_1.
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
  assert (H_RC: RC k (Ty_IFix F T) rho eb_ms eb'_ms) by eauto.
  autorewrite with RC in H_RC.
  destruct H_RC as [_ [_ H_RC]].
  remember (H_RC j_1 Hlt__j_1 e_f1 Hev__e) as temp.
  clear Heqtemp. clear H_RC. rename temp into H_RC.

  (** 
      Hence, there exists e'_f1 (and j'_1) such that
      # e' =[j'_1]=> e'_f1, and
      # (k - j_1, e_f1, e'_f1) \in RV[[Ty_IFix F T]]
  *)
  destruct H_RC as [e'_f1 [j'_1 [Hev__e1' H_RC]]].
  assert (H_RV: RC (k - j_1) (Ty_IFix F T) rho e_f1 e'_f1). {
    eapply RC_monotone.
    - eapply eval_preserves_R; eauto.
      split.
      + eauto.
      + eauto.
    - apply helper2. assumption.
  }

  (**
      Hence, 
        e_f1 `equiv` IWrap F T v_f11, and
        e'_f1 `equiv` IWrap F T v'_f11.
  *)
  assert (temp: exists v_f11, e_f1 = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_f11). {
    apply skip. (* TODO *)
  }
  destruct temp as [v_f11 Heq1].
  assert (temp: exists v'_f11, e'_f1 = IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_f11). {
    apply skip. (* TODO *)
  }
  destruct temp as [v'_f11 Heq2].

  (**
      Note that
        Unwrap e -[j_1]->
        Unwrap e_f1 =
        Unwrap (IWrap F T v_f11) -[1]->
        v_f11 -[j - j1 - 1]->
        e_f

        Since v_f11 is a value, we have irred(v_f11).
        Hence, j - j_1 -1 = 0 (and j = j_1 + 1) and e_f `equiv` v_f11.
  *)
  assert (temp: j - j_1 - 1 = 0 /\ j = j_1 + 1 /\ e_f = v_f11). {
    subst. eapply inspect_eval__Unwrap_2; eauto. split; eauto.
  }
  destruct temp as [Heq3 [Heq4 Heq5]].

  (**
      Furthermore, note that
        Unwrap e' -[j'_1]-> 
        Unwrap e'_f1 =
        Unwrap (IWrap F T v'_f11) -[1]->
        v'_f11

      Since v'_f11 is a value, we have irred(v'_f11).
      Let e'f = v'_f11.
  *)
  exists (v'_f11). exists (j'_1 + 1).
  
  (** messy below *)
  split. {
    subst. eapply E_Unwrap; eauto.
  }

  assert (IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_f11 = IWrap (msubstT (msyn1 rho) F) (msubstT (msyn1 rho) T) v_f11) by reflexivity.
  assert (IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_f11 = IWrap (msubstT (msyn2 rho) F) (msubstT (msyn2 rho) T) v'_f11) by reflexivity.
  assert (k - j < k - j_1) by (eapply helper3; eauto).
  subst.
  assert (Hkind_msT: empty |-* (msubstT (msyn2 rho) T) : K). {
    apply skip. (* TODO *)
  }
  remember (H_RC _ _ H H0 _ H1 _ _ Hkind_msT Hnorm) as H_RC2.
  clear HeqH_RC2.

  assert (terminates_excl v_f11 0 v_f11 (k - (j_1 + 1))). {
    split.
    + eapply eval_value.
      eapply eval_to_value.
      eauto.
    + eapply helper4; eauto.
  }

  autorewrite with RC in H_RC2.

  destruct H_RC2 as [_ [_ H_RC2]].
  assert (0 < k - (j_1 + 1)). {
    eapply helper4; eauto.
  }
  assert (v_f11 =[0]=> v_f11). {
    eapply eval_value. eapply eval_to_value; eauto.
  }

  eapply H_RC2 in H3; eauto.
  destruct H3.
  destruct H3.
  destruct H3.

  assert (v'_f11 =[0]=> v'_f11). {
    eapply eval_value. eapply eval_to_value; eauto. eapply E_Unwrap; eauto.
  }

  assert (x = v'_f11) by (eapply eval__deterministic; eauto).
  subst.
  rewrite <- minus_n_O in H5.
  eauto.

  Unshelve. all: eauto.
Qed.