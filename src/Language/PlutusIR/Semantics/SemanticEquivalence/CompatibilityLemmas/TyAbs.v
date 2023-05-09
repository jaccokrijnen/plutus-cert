Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.

Require Import Arith.



Lemma msubst_TyAbs : forall ss bX K t0,
    msubst_term ss (TyAbs bX K t0) = TyAbs bX K (msubst_term ss t0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_TyAbs : forall ss bX K t0,
    msubstA_term ss (TyAbs bX K t0) = TyAbs bX K (msubstA_term (drop bX ss) t0).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.


Lemma msubstT_TyForall : forall ss bX K T,
    msubstT ss (Ty_Forall bX K T) = Ty_Forall bX K (msubstT (drop bX ss) T).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX)%string; eauto. Qed.


Lemma compatibility_TyAbs: forall Δ Γ bX K T e e',
    LR_logically_approximate ((bX, K) :: Δ) Γ e e' T ->
    LR_logically_approximate Δ Γ (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof with eauto_LR.
  intros Δ Γ bX K T e e' IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split... 

  intros k ρ γ γ' HRD HRG.

  autorewrite with RC.

  rewrite msubstA_TyAbs. rewrite msubstA_TyAbs.
  rewrite msubst_TyAbs. rewrite msubst_TyAbs.
  rewrite msubstT_TyForall. rewrite msubstT_TyForall.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  
  eexists. eexists.

  split. {
    eapply eval_value__value. apply V_TyAbs.
  }

  split... {
    apply T_TyAbs in Htyp__e.
    eapply has_type__basekinded in Htyp__e as H...
    eapply closing_preserves_kinding_1 in H as H0...
    rewrite msubstT_TyForall in H0.
    apply strong_normalisation in H0 as H1.
    destruct H1.
    inversion H1. subst.
    eexists. split...
    eapply closingA_preserves_typing_1 in Htyp__e...
    2: {
      rewrite msubstT_TyForall...
    }
    eapply closing_preserves_typing_1 in Htyp__e...
    rewrite msubstA_TyAbs in Htyp__e.
    rewrite msubst_TyAbs in Htyp__e.
    eauto.
  }
  split... {
    apply T_TyAbs in Htyp__e'.
    eapply has_type__basekinded in Htyp__e' as H...
    eapply closing_preserves_kinding_2 in H as H0...
    rewrite msubstT_TyForall in H0.
    apply strong_normalisation in H0 as H1.
    destruct H1.
    inversion H1. subst.
    eexists. split...
    eapply closingA_preserves_typing_2 in Htyp__e'...
    2: {
      rewrite msubstT_TyForall...
    }
    eapply closing_preserves_typing_2 in Htyp__e'...
    rewrite msubstA_TyAbs in Htyp__e'.
    rewrite msubst_TyAbs in Htyp__e'.
    eauto.
  }

  left. split. intros Hcon. inversion Hcon. split. intros Hcon. inversion Hcon.

  eexists. eexists.
  
  split... split...

  intros.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.
  
  eapply IH__e.
  - eapply RD_cons; eauto.
  - apply RG_extend_rho.
    eapply RG_monotone; eauto.
    rewrite <- minus_n_O in Hlt_i.
    apply Nat.lt_le_incl.
    assumption.
Qed.
