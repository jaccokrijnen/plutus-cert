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

Lemma RC_compatibility_Unwrap : forall k F K T e e',
    emptyContext |-* T : K ->
    RC k (Ty_IFix F T) e e' ->
    RC k (beta_reduce (unwrapIFix F K T)) (Unwrap e) (Unwrap e').
Proof.
  intros k F K T e e'.
  intros Hkind_T H_RC.
  remember H_RC as H_RC'. clear HeqH_RC'.

  assert (Htyp : emptyContext |-+ (Unwrap e) : (beta_reduce (unwrapIFix F K T))). {
    eapply T_Unwrap; eauto.
    eapply RC_typable_empty_1; eauto.
  } 
  assert (Htyp' : emptyContext |-+ (Unwrap e') : (beta_reduce (unwrapIFix F K T))). {
    eapply T_Unwrap; eauto.
    eapply RC_typable_empty_2; eauto.
  }

  autorewrite with RC.

  (* First part of the proof *)
  split; auto. split; auto.

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
  assert (temp: exists j_1 e_f1, e =[j_1]=> e_f1 /\ j_1 <= j) by eauto using inspect_eval__Unwrap_1.
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
      # (k - j_1, e_f1, e'_f1) \in RV[[Ty_IFix F T]]
  *)
  destruct H_RC as [e'_f1 [j'_1 [Hev__e1' H_RC]]].
  assert (H_RV: RC (k - j_1) (Ty_IFix F T) e_f1 e'_f1). {
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

  (**
      Hence, 
        e_f1 `equiv` IWrap F T v_f11, and
        e'_f1 `equiv` IWrap F T v'_f11.
  *)
  assert (temp: exists v_f11, e_f1 = IWrap F T v_f11). {
    apply skip. (* TODO *)
  }
  destruct temp as [v_f11 Heq1].
  assert (temp: exists v'_f11, e'_f1 = IWrap F T v'_f11). {
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

  assert (IWrap F T v_f11 = IWrap F T v_f11) by reflexivity.
  assert (IWrap F T v'_f11 = IWrap F T v'_f11) by reflexivity.
  assert (k - j < k - j_1) by (eapply helper3; eauto).
  subst.
  remember (H_RC _ _ H H0 _ H1 _ Hkind_T) as H_RC2.
  clear HeqH_RC2.

  assert (terminates_excl v_f11 0 v_f11 (k - (j_1 + 1))). {
    split.
    + eapply eval_value.
      eapply eval_to_value.
      eauto.
    + eapply helper4; eauto.
  }

  destruct (beta_reduce (unwrapIFix F K T)) eqn:Hd.
  - eapply RC_impossible_type in H_RC2; eauto.

  - eapply RC_functional_extensionality in H_RC2; eauto.
    destruct H_RC2 as [a [b [c H_RC2]]].
    assert (a = v'_f11 /\ b = 0). {
      
      eapply eval__deterministic; eauto.
      apply eval_value.
      eapply eval_to_value; eauto.
      eapply E_Unwrap. eauto.
    }
    destruct H3. subst.

    intros.
    eapply H_RC2; eauto.
    rewrite <- minus_n_O.
    auto.

  - eapply RC_unwrap in H_RC2; eauto.
    destruct H_RC2 as [a [b [c H_RC2]]].
    assert (a = v'_f11 /\ b = 0). {
      
      eapply eval__deterministic; eauto.
      apply eval_value.
      eapply eval_to_value; eauto.
      eapply E_Unwrap. eauto.
    }
    destruct H3. subst.

    intros.
    eapply H_RC2; eauto.
    rewrite <- minus_n_O.
    auto.

  - eapply RC_instantiational_extensionality in H_RC2; eauto.
    destruct H_RC2 as [a [b [c H_RC2]]].
    assert (a = v'_f11 /\ b = 0). {
      
      eapply eval__deterministic; eauto.
      apply eval_value.
      eapply eval_to_value; eauto.
      eapply E_Unwrap. eauto.
    }
    destruct H3. subst.

    intros.
    eapply H_RC2; eauto.
    rewrite <- minus_n_O.
    auto.

  - eapply RC_syntactic_equality in H_RC2; eauto.
    destruct H_RC2 as [a [b [c H_RC2]]].
    assert (a = v'_f11 /\ b = 0). {
      
      eapply eval__deterministic; eauto.
      apply eval_value.
      eapply eval_to_value; eauto.
      eapply E_Unwrap. eauto.
    }
    destruct H3. subst.

    intros.
    eapply H_RC2; eauto.

  - eapply RC_impossible_type in H_RC2; eauto.

  - eapply RC_impossible_type in H_RC2; eauto.
Qed.