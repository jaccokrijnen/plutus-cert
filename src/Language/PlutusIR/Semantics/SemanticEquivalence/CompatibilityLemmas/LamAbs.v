Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.


Lemma msubst_LamAbs : forall ss x T t0,
    msubst_term ss (LamAbs x T t0) = LamAbs x T (msubst_term (drop x ss) t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    simpl.
    destruct (s =? x) eqn:Heqb.
    + eauto using eqb_eq.
    + eauto using eqb_neq.
Qed.

Lemma msubstA_LamAbs : forall ss x T t0,
    msubstA_term ss (LamAbs x T t0) = LamAbs x (msubstT ss T) (msubstA_term ss t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_term__fold : forall ss x v t,
    msubst_term ss <{ [v / x] t }> = msubst_term ((x, v) :: ss) t.
Proof. induction ss; intros; auto. Qed.


Lemma compatibility_LamAbs : forall Delta Gamma x T1 e e' T2,
    Delta |-* T1 : Kind_Base ->
    LR_logically_approximate Delta (x |-> T1; Gamma) e e' T2 ->
    LR_logically_approximate Delta Gamma (LamAbs x T1 e) (LamAbs x T1 e') (Ty_Fun T1 T2).
Proof with eauto_LR.
  intros Delta Gamma x T1 eb eb' T2 Hkind__T1 IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  split...
  split...

  rewrite msubstA_LamAbs. rewrite msubstA_LamAbs.
  rewrite msubst_LamAbs. rewrite msubst_LamAbs.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  
  eexists. eexists.

  split. eapply eval_value. apply V_LamAbs.

  left.

  eexists. eexists. eexists. eexists.

  split...
  split...

  rewrite <- minus_n_O.
  intros i Hlt__i v_0 v'_0 HRV.

  apply RV_unfolded_to_RV in HRV.

  assert (closed v_0) by eauto using RV_typable_empty_1, typable_empty__closed.
  assert (closed v'_0) by eauto using RV_typable_empty_2, typable_empty__closed.
  eapply RG_env_closed in H_RG as Hclss.
  destruct Hclss as [Hcls__env Hcls__env'].

  rewrite <- subst_msubst...
  rewrite <- subst_msubst...
  rewrite msubst_term__fold.
  rewrite msubst_term__fold. 

  eapply IH...
  + apply mupdate_unfold.
  + replace v_0 with (msubstA_term (msyn1 rho) v_0) by eauto using msubstA_closed.
    replace v'_0 with (msubstA_term (msyn2 rho) v'_0) by eauto using msubstA_closed.
    eapply RG_cons...
    * rewrite msubstA_closed...
      rewrite msubstA_closed...
    * eapply RG_monotone...
Qed.