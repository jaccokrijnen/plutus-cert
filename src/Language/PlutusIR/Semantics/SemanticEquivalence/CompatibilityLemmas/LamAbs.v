Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.


Lemma msubst_LamAbs : forall ss x T t0 t',
    closed_env ss ->
    msubst ss (LamAbs x T t0) t' ->
    exists t0', msubst (drop x ss) t0 t0' /\ t' = LamAbs x T t0'.
Proof.
  induction ss.
  - intros. 
    inversion H0. subst.
    exists t0.
    split. 
    + apply msubst_nil.
    + reflexivity. 
  - intros.
    inversion H0. subst.
    rename t'0 into t''.
    destruct H.
    inversion H3.
    + subst.
      simpl.
      rewrite eqb_refl.
      eapply IHss; eauto.
    + subst.
      simpl.
      apply eqb_neq in H10.
      rewrite H10.
      edestruct IHss as [t0'' Hms0']; eauto.
      eexists.
      split.
      -- eapply msubst_cons.
         ++ apply H11.
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
    (Delta, Gamma) |-* T1 : Kind_Base ->
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

  assert (Hcls1 : closed_env env) by (eapply RG_env_closed_1; eauto).
  assert (Hcls2 : closed_env env') by (eapply RG_env_closed_2; eauto).
  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e_sa) as [eb_sa [HmsA__eb_sa Heq]].
  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e'_sa) as [eb'_sa [HmsA__eb'_sa Heq']].
  subst.
  destruct (msubst_LamAbs _ _ _ _ _ Hcls1 Hms__e_s) as [eb_s [Hms__eb_s Heq]].
  destruct (msubst_LamAbs _ _ _ _ _ Hcls2 Hms__e'_s) as [eb'_s [Hms__eb'_s Heq']].
  subst.
  clear Hcls1 Hcls2.

  unfold LR_logically_approximate in IH_LR.

  autorewrite with RC.
  split. {
    eapply msubst_preserves_typing_1; eauto.
    rewrite msubstT_TyFun.
    destruct IH_LR.
    eapply T_LamAbs.
Abort.
(*
    + eauto.


    apply skip.
  }
  split. {
    apply skip.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (LamAbs x (msubstT (msyn2 rho) T1) eb'_s).
  exists 0.
  split. {
    eapply eval_value. apply V_LamAbs.
  }
  intros.

  eapply IH_LR.
  - reflexivity.
  - reflexivity. 

  inversion H1. subst.
  inversion H2. subst.

  assert (msubst ((x', v) :: drop x' e1) t0_1 e_body'). { apply skip. }
  assert (msubst ((x', v') :: drop x' e2) t0_1 e'_body'). { apply skip. }

  eapply IH; eauto.
  + assert (x' |T-> T1; mupdate emptyContext c = mupdate emptyContext ((x', T1) :: drop x' c)). {
      apply skip.
    }
    apply H10.
  + apply V_cons; eauto.
    eapply instantiation_drop.
    apply skip.
*)