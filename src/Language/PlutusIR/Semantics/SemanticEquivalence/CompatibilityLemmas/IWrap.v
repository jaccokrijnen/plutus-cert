Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.ReductionInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Termination.

Require Import Arith.
Require Import Coq.Logic.Decidable.

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

Lemma RC_compatibility_IWrap : forall k F K T e e',
    emptyContext |-* T : K ->
    emptyContext |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
    RC k (beta_reduce (unwrapIFix F K T)) e e' ->
    RC k (Ty_IFix F T) (IWrap F T e) (IWrap F T e').
Proof.
  intros k F K T e e'.
  intros Hkind_T Hkind_F H_RC.
  remember H_RC as H_RC'. clear HeqH_RC'.

  assert (Htyp : emptyContext |-+ (IWrap F T e) : (Ty_IFix F T)). {
    eapply T_IWrap; eauto.
    eapply RC_typable_empty_1; eauto.
  } 
  assert (Htyp' : emptyContext |-+ (IWrap F T e') : (Ty_IFix F T)). {
    eapply T_IWrap; eauto.
    eapply RC_typable_empty_2; eauto.
  }

  autorewrite with RC.

  (* First part of the proof *)
  split; auto. split; auto.

  (* Second part of the proof *)

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
  assert (temp: exists j_1 e_f1, e =[j_1]=> e_f1 /\ j_1 <= j) by eauto using inspect_eval__IWrap_1.
  destruct temp as [j_1 [e_f1 [Hev__e Hle__j_1]]].

  (** 
      Instantiate the second conjunct of H_RC with k. ... Instantiate this with 
      j_1, e_f1. Note that
      # j_1 < k, which follows from j_1 <= j < k,
      # e =[j_1]=> e_f1, and
      # irred(e_f1)
  *)
  assert (Hlt__j_1 : j_1 < k) by eauto using Nat.le_lt_trans. 

  autorewrite with RC in H_RC.
  destruct H_RC as [_ [_ H_RC]].
  remember (H_RC j_1 Hlt__j_1 e_f1 Hev__e) as temp.
  clear Heqtemp. clear H_RC. rename temp into H_RC.

  (** 
      Hence, there exists e'_f1 (and j'_1) such that
      # e' =[j'_1]=> e'_f1, and
      # (k - j_1, e_f1, e'_f1) \in RV[[beta_reduce (unwrapIFix F K T)]]
  *)
  destruct H_RC as [e'_f1 [j'_1 [Hev__e1' H_RC]]].
  assert (H_RV: RC (k - j_1) (beta_reduce (unwrapIFix F K T)) e_f1 e'_f1). {
    eapply RC_monotone.
    - split.
      + eapply eval_value. eapply eval_to_value. eauto.
      + eapply helper1; eauto. 
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
  assert (temp: j - j_1 = 0 /\ j = j_1 /\ e_f = IWrap F T v_f1). {
    eapply inspect_eval__IWrap_2; eauto. split; auto.
  }
  destruct temp as [Heq1 [Heq2 Heq3]].

  (**
      Let e'_f = IWrap F T v'_f1 (and j' = j'_1)
  *)
  exists (IWrap F T v'_f1). exists j'_1.
  
  (** messy below *)
  split. {
    eapply E_IWrap; eauto.
  }

  intros v v' Heq4 Heq5 i Hlt__i K0 Hkind_K0.
  subst. inversion Heq4. subst.
  inversion Heq5. subst.

  assert (K0 = K) by eauto using unique_kinds.
  subst.

  eapply RV_monotone.
  + eapply eval_to_value. eauto.
  + apply helper3. apply Hlt__j_1.
  + assumption.
  + apply helper4.
    assumption.
Qed.