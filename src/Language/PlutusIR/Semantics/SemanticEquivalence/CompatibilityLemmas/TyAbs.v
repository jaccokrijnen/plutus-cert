Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.


Lemma msubst_TyAbs : forall ss bX K t0 t',
    msubst ss (TyAbs bX K t0) t' ->
    exists t0', msubst ss t0 t0' /\ t' = TyAbs bX K t0'.
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
    subst.
    edestruct IHss as [t0'' Hms0']; eauto.
    eexists.
    split.
    + eapply msubst_cons.
      * apply H8.
      * apply Hms0'.
    + destruct Hms0'.
      * subst.
        reflexivity.
Qed.

Lemma msubstA_TyAbs : forall ss bX K t0 t',
    msubstA ss (TyAbs bX K t0) t' ->
    exists t0', msubstA (drop bX ss) t0 t0' /\ t' = TyAbs bX K t0'.
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
    + subst.
      simpl.
      rewrite eqb_refl.
      eauto.
    + subst.
      simpl.
      apply eqb_neq in H8.
      rewrite H8.
      edestruct IHss as [t0'' [HmsA__t0'' Heq]]; eauto.
      subst.
      eexists.
      split.
      * eapply msubstA_cons. eauto. eauto.
      * reflexivity. 
Qed.

Lemma msubstT_TyForall : forall ss bX K T,
    msubstT ss (Ty_Forall bX K T) = Ty_Forall bX K (msubstT (drop bX ss) T).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    destruct (s =? bX) eqn:Heqb.
    + eauto.
    + eauto.
Qed.


Lemma compatibility_TyAbs: forall Delta Gamma bX K T e e',
    LR_logically_approximate (bX |-> K; Delta) Gamma e e' T ->
    LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof.
  intros Delta Gamma bX K T e e' IH_LR.
  unfold LR_logically_approximate.

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_TyAbs. auto.
  }

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_TyAbs. auto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_sa e'_sa e_s e'_s.
  intros HmsA__e_sa HmsA__e'_sa Hms__e_s Hms__e'_s.

  destruct (msubstA_TyAbs _ _ _ _ _ HmsA__e_sa) as [eb_sa [HmsA__eb_sa Heq]].
  destruct (msubstA_TyAbs _ _ _ _ _ HmsA__e'_sa) as [eb'_sa [HmsA__eb'_sa Heq']].
  subst.
  destruct (msubst_TyAbs _ _ _ _ _ Hms__e_s) as [eb_s [Hms__eb_s Heq]].
  destruct (msubst_TyAbs _ _ _ _ _ Hms__e'_s) as [eb'_s [Hms__eb'_s Heq']].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR.
      eapply T_TyAbs; eauto.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR.
      eapply T_TyAbs; eauto.
    - rewrite mupd_empty; eauto.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (TyAbs bX K eb'_s).
  exists 0.
  split. {
    eapply eval_value. apply V_TyAbs.
  }
  intros.
  symmetry in H. inversion H. subst.
  symmetry in H0. inversion H0. subst.

  (*
  assert (exists v_sa, msubstA (msyn1 ((bX, (Chi, T1, T2)) :: rho)) v v_sa) by eapply msubstA_total.
  destruct H4 as [v_sa Hmsa__v_sa].
  assert (v_sa = v). { eapply msubstA_closed; eauto. eapply typable_empty__closed. eapply RC_typable_empty_1. eapply H1. }
  subst.
  assert (exists v'_sa, msubstA (msyn2 rho) v' v'_sa) by eapply msubstA_total.
  destruct H4 as [v'_sa Hmsa__v'_sa].
  assert (v'_sa = v'). { eapply msubstA_closed; eauto. eapply typable_empty__closed. eapply RC_typable_empty_2. eapply H1. }
  subst.
  *)

  (*
  assert (exists aaa, substituteA bX T1 e aaa) by eapply substituteA_total.
  destruct H6 as [aaa Haaa].
  assert (exists bbb, msubstA (msyn1 rho) aaa bbb) by eauto using msubstA_total.
  destruct H6 as [bbb Hbbb].
  assert (bbb = eb_sa). {
    eapply substA_msubstA; eauto.
    - eapply typable_empty__closed_Ty.
      eauto.
    -  eapply RG_env_closed_1. eauto.
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
  }*)

  unfold LR_logically_approximate in IH_LR.
  destruct IH_LR as [_ [_ IH_LR]].
  eapply IH_LR.
  - rewrite mupdate_unfold. reflexivity.
  - reflexivity.
  - split.
    + eapply RD_cons; eauto.
    + apply RG_extend_rho.
      eapply RG_monotone; eauto.
      rewrite <- minus_n_O in Hlt_i.
      apply Nat.lt_le_incl.
      assumption.
  - apply skip.
  - apply skip.
  - apply skip.
  - apply skip.

  Unshelve. all: eauto.
Qed.