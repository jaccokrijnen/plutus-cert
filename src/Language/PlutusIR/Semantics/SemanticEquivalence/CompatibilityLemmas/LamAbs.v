Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.


Lemma msubst_LamAbs : forall ss x T t0,
    msubst_term ss (LamAbs x T t0) = LamAbs x T (msubst_term (drop x ss) t0).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    simpl.
    destruct (s =? x)%string eqn:Heqb.
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
    msubst_term ss <{ [v / x] t }> = msubst_term ((x, v) :: ss)%list t.
Proof. induction ss; intros; auto. Qed.


Lemma compatibility_LamAbs : forall Delta Gamma x T1 T1n T2n e e',
    Delta |-* T1 : Kind_Base ->
    normalise T1 T1n ->
    LR_logically_approximate Delta (x |-> T1n; Gamma) e e' T2n ->
    LR_logically_approximate Delta Gamma (LamAbs x T1 e) (LamAbs x T1 e') (Ty_Fun T1n T2n).
Proof with eauto_LR.
  intros Delta Gamma x T1 T1n T2n eb eb' Hkind__T1 Hnorm__T1n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_LamAbs. rewrite msubstA_LamAbs.
  rewrite msubst_LamAbs. rewrite msubst_LamAbs.
  rewrite msubstT_TyFun. rewrite msubstT_TyFun.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  
  
  eexists. eexists.

  split... eapply E_LamAbs...

  split... {
    rewrite <- msubst_LamAbs. rewrite <- msubstA_LamAbs.
    eapply preservation in Hkind__T1 as H...
    eapply msubstT_preserves_kinding_1 in H as H0...
    eapply has_type__basekinded in Htyp__e as H1.
    eapply msubstT_preserves_kinding_1 in H1 as H2...
    apply K_Fun with (T1 := msubstT (msyn1 rho) T1n) in H2 as H3...
    eapply strong_normalisation in H3 as H4.
    destruct H4.
    exists x0...
    split...
    inversion H4. subst.
    replace (@empty Ty) with (mgsubst (msyn1 rho) empty) by eauto using mgsubst_empty.
    eapply msubst_preserves_typing_1...
    eapply msubstA_preserves_typing_1...
    rewrite msubstT_TyFun.
    econstructor...
  }
  split... {
    rewrite <- msubst_LamAbs. rewrite <- msubstA_LamAbs.
    eapply preservation in Hkind__T1 as H...
    eapply msubstT_preserves_kinding_2 in H as H0...
    eapply has_type__basekinded in Htyp__e' as H1.
    eapply msubstT_preserves_kinding_2 in H1 as H2...
    apply K_Fun with (T1 := msubstT (msyn2 rho) T1n) in H2 as H3...
    eapply strong_normalisation in H3 as H4.
    destruct H4.
    exists x0...
    split...
    inversion H4. subst.
    replace (@empty Ty) with (mgsubst (msyn2 rho) empty) by eauto using mgsubst_empty.
    eapply msubst_preserves_typing_2...
    eapply msubstA_preserves_typing_2...
    rewrite msubstT_TyFun.
    econstructor...
  }

  left.

  split... intros Hcon. inversion Hcon.
  split... intros Hcon. inversion Hcon.

  eexists. eexists. eexists. eexists. eexists.

  split...
  split...
  split...

  rewrite <- minus_n_O. 
  intros i Hlt__i v_0 v'_0 HRV.

  apply RV_unfolded_to_RV in HRV.

  apply RC_lt_obsolete.
  
  intros Hlt.

  assert (Hcls__v_0 : closed v_0). {
    eapply RV_typable_empty_1 in HRV...
    destruct HRV as [H [H0 H1]].
    eapply typable_empty__closed...
  }
  assert (Hcls__v'_0 : closed v'_0). {
    eapply RV_typable_empty_2 in HRV...
    destruct HRV as [H [H0 H1]].
    eapply typable_empty__closed...
  }
  
  eapply RG_env_closed in H_RG as Hclss...
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