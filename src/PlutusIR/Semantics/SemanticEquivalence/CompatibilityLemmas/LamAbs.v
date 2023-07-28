Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.
Require Import Lists.List.
Import ListNotations.


Lemma compatibility_LamAbs : forall Delta Gamma x T1 T1n T2n e e',
    Delta |-* T1 : Kind_Base ->
    normalise T1 T1n ->
    LR_logically_approximate Delta ((x, T1n) :: Gamma) e e' T2n ->
    LR_logically_approximate Delta Gamma (LamAbs x T1 e) (LamAbs x T1 e') (Ty_Fun T1n T2n).
Proof with eauto_LR.
  intros Delta Gamma x T1 T1n T2n eb eb' Hkind__T1 Hnorm__T1n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

  split...
  split...

  intros k rho env env' H_RD H_RG.
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
    eapply closing_preserves_kinding_1 in H as H0...
    eapply has_type__basekinded in Htyp__e as H1.
    eapply closing_preserves_kinding_1 in H1 as H2...
    apply K_Fun with (T1 := msubstT (msyn1 rho) T1n) in H2 as H3...
    eapply strong_normalisation in H3 as H4.
    destruct H4.
    exists x0...
    split...
    inversion H4. subst.
    replace (@nil (string * Ty)) with (mgsubst (msyn1 rho) []) by eauto using mgsubst_empty.
    eapply msubst_preserves_typing_1...
    rewrite app_nil_r.
    eapply msubstA_preserves_typing_1...
    rewrite app_nil_r.
    econstructor...
    rewrite msubstT_TyFun...
  }
  split... {
    rewrite <- msubst_LamAbs. rewrite <- msubstA_LamAbs.
    eapply preservation in Hkind__T1 as H...
    eapply closing_preserves_kinding_2 in H as H0...
    eapply has_type__basekinded in Htyp__e' as H1.
    eapply closing_preserves_kinding_2 in H1 as H2...
    apply K_Fun with (T1 := msubstT (msyn2 rho) T1n) in H2 as H3...
    eapply strong_normalisation in H3 as H4.
    destruct H4.
    exists x0...
    split...
    inversion H4. subst.
    replace (@nil (string * Ty)) with (mgsubst (msyn2 rho) []) by eauto using mgsubst_empty.
    eapply msubst_preserves_typing_2...
    eapply msubstA_preserves_typing_2...
    repeat rewrite app_nil_r.
    econstructor...
    rewrite msubstT_TyFun...
  }

  left.

  split... intros Hcon. inversion Hcon.
  split... intros Hcon. inversion Hcon.

  eexists. eexists. eexists. eexists. eexists.

  split...
  split...

  rewrite <- minus_n_O.
  intros i Hlt__i v_0 v'_0 [H_pure_v_0 H_pure_v'_0] HRV.

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
  rewrite msubst__fold.
  rewrite msubst__fold.

  eapply IH...
  + econstructor...
    eapply RG_monotone...
Qed.
