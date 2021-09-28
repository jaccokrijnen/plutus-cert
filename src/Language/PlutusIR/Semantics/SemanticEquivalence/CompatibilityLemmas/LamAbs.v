Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.


Lemma msubst_LamAbs : forall ss x T t0 t',
    msubst ss (LamAbs x T t0) t' ->
    exists t0', msubst (drop x ss) t0 t0' /\ t' = LamAbs x T t0'.
Proof.
  induction ss.
  - intros. 
    inversion H. subst.
    exists t0.
    split. 
    + apply msubst_nil.
    + reflexivity. 
  - intros.
    inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    + subst.
      simpl.
      rewrite eqb_refl.
      eapply IHss; eauto.
    + subst.
      simpl.
      apply eqb_neq in H8.
      rewrite H8.
      edestruct IHss as [t0'' Hms0']; eauto.
      eexists.
      split.
      -- eapply msubst_cons.
         ++ apply H9.
         ++ apply Hms0'.
      -- destruct Hms0'.
         subst.
         reflexivity.
Qed.

Lemma msubstA_LamAbs : forall ss x T t0 t',
    msubstA ss (LamAbs x T t0) t' ->
    exists t0', msubstA ss t0 t0' /\ t' = LamAbs x (msubstT ss T) t0'.
Proof.
  induction ss.
  - intros. 
    inversion H. subst.
    exists t0.
    split. 
    + apply msubstA_nil.
    + reflexivity. 
  - intros.
    inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    subst.
    simpl.
    edestruct IHss as [t0'' [HmsA__t0'' Heq]]; eauto.
    subst.
    eexists.
    split.
    + eapply msubstA_cons. eauto. eauto.
    + reflexivity. 
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    apply IHss.
Qed.


Lemma compatibility_LamAbs : forall Delta Gamma x T1 e e' T2,
    Delta |-* T1 : Kind_Base ->
    LR_logically_approximate Delta (x |-> T1; Gamma) e e' T2 ->
    LR_logically_approximate Delta Gamma (LamAbs x T1 e) (LamAbs x T1 e') (Ty_Fun T1 T2).
Proof.
  intros Delta Gamma x T1 eb eb' T2 Hkind__T1 IH_LR.
  unfold LR_logically_approximate.

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_LamAbs. auto. auto.
  }

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_LamAbs. auto. auto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_sa e'_sa e_s e'_s.
  intros HmsA__e_sa HmsA__e'_sa Hms__e_s Hms__e'_s.

  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e_sa) as [eb_sa [HmsA__eb_sa Heq]].
  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e'_sa) as [eb'_sa [HmsA__eb'_sa Heq']].
  subst.
  destruct (msubst_LamAbs _ _ _ _ _ Hms__e_s) as [eb_s [Hms__eb_s Heq]].
  destruct (msubst_LamAbs _ _ _ _ _ Hms__e'_s) as [eb'_s [Hms__eb'_s Heq']].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR.
      eapply T_LamAbs; eauto.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR. destruct H0.
      eapply T_LamAbs; eauto.
    - rewrite mupd_empty; eauto.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (LamAbs x (msubstT (msyn2 rho) T1) eb'_s).
  exists 0.
  split. {
    eapply eval_value. apply V_LamAbs.
  }
  intros.
  symmetry in H. inversion H. subst.
  symmetry in H0. inversion H0. subst.

  assert (exists v_sa, msubstA (msyn1 rho) v v_sa) by eapply msubstA_total.
  destruct H4 as [v_sa Hmsa__v_sa].
  assert (v_sa = v). { eapply msubstA_closed; eauto. eapply typable_empty__closed. eapply RC_typable_empty_1. eapply H1. }
  subst.
  assert (exists v'_sa, msubstA (msyn2 rho) v' v'_sa) by eapply msubstA_total.
  destruct H4 as [v'_sa Hmsa__v'_sa].
  assert (v'_sa = v'). { eapply msubstA_closed; eauto. eapply typable_empty__closed. eapply RC_typable_empty_2. eapply H1. }
  subst.

  assert (exists aaa, substitute x v eb_sa aaa) by eauto using substitute_models_total_function__Term.
  destruct H4 as [aaa Haaa].
  assert (exists bbb, msubst env aaa bbb) by eauto using msubst_total.
  destruct H4 as [bbb Hbbb].
  assert (bbb = e_body'). {
    eapply subst_msubst; eauto.
    - eapply typable_empty__closed.
      eapply RC_typable_empty_1.
      eapply H1.
    - eapply RG_env_closed_1. eauto.
  }
  subst.
  assert (msubst ((x, v) :: env) eb_sa e_body'). {
    econstructor; eauto.
  }

  assert (exists ccc, substitute x v' eb'_sa ccc) by eauto using substitute_models_total_function__Term.
  destruct H5 as [ccc Hccc].
  assert (exists ddd, msubst env' ccc ddd) by eauto using msubst_total.
  destruct H5 as [ddd Hddd].
  assert (ddd = e'_body'). {
    eapply subst_msubst; eauto.
    - eapply typable_empty__closed.
      eapply RC_typable_empty_2.
      eapply H1.
    - eapply RG_env_closed_2. eauto.
  }
  subst.
  assert (msubst ((x, v') :: env') eb'_sa e'_body'). {
    econstructor; eauto.
  }

  unfold LR_logically_approximate in IH_LR.
  destruct IH_LR as [_ [_ IH_LR]].
  eapply IH_LR.
  - reflexivity.
  - rewrite mupdate_unfold.  reflexivity.
  - split; auto.
    eapply RG_cons.
    + apply Hmsa__v_sa.
    + apply Hmsa__v'_sa.
    + apply H1.
    + apply H1.
    + apply H1.
    + eapply RG_monotone; eauto.
      rewrite <- minus_n_O in Hlt_i.
      apply Nat.lt_le_incl.
      assumption.
  - eassumption.
  - eassumption.
  - apply H4.
  - apply H5.
Qed.