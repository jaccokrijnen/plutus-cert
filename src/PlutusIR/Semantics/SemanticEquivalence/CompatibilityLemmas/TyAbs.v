Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
From PlutusCert Require Import SubstitutionPreservesTyping.

Require Import Arith.

Require Import PlutusCert.Util.Tactics.
Require Import Lists.List.

Lemma drop_ty_var__RG ρ k Γ γ γ' : forall bX,
  RG ρ k Γ γ γ' ->
    exists γ_dropped γ_dropped',
      RG ρ k (drop_ty_var bX Γ) γ_dropped γ_dropped'.
Proof.
  induction 1.
  - eexists nil, nil. eauto using RG.
  - simpl.
    destruct_hypos.
    destruct_if.
    + revert H_eqb. destruct_if.
      * inversion 1.
      * eauto using RG.
    + revert H_eqb. destruct_if.
      * intros _. eauto.
      * inversion 1.
Qed.

Open Scope string_scope.
Import ListNotations.

Lemma drop_RG k Γ ρ γ γ' x :
  0 < k ->
  RG ρ k Γ γ γ' ->
  RG ρ k (drop x Γ) (drop x γ) (drop x γ')
.
Proof.
  induction 2; simpl.
  - constructor.
  - destruct (x0 =? x);
    eauto using RG.
Qed.

Definition c γ δ t := msubst γ (msubstA δ t).


Lemma msubst__Var x n γ : 
  x <> n -> msubst γ (Var n) = msubst (drop x γ) (Var n).
Proof.
Admitted.

Lemma drop_msubst x t γ δ: forall Δ Γ T,
    Δ ,, drop x Γ |-+ t : T -> (* i.e. x not free in t *)
    msubst γ (msubstA δ t) = msubst (drop x γ) (msubstA δ t).
Proof.
  induction t; intros Δ Γ T H_ty.
  - admit.
  - (* Var *)
    inversion H_ty; subst.
    assert (x <> n) by admit. (* from lookup *)
    assert (msubstA δ (Var n) = Var n) by admit.
    rewrite H1.
    erewrite msubst__Var; eauto.
  - (* TyAbs *)
    autorewrite with multi_subst.
    inversion H_ty;subst.
    admit.
Admitted.

(* Version that also works for Δ *)
Lemma drop_RG__msubst_1 k Γ γ γ' x Δ ρ:
  0 < k -> (* is this necessary?  *)
  RD Δ ρ ->
  RG ρ k Γ γ γ' ->
  forall t T,
    Δ ,, drop x Γ |-+ t : T ->
    RG ρ k (drop x  Γ) (drop x γ) (drop x γ') /\
    c γ (msyn1 ρ) t = c (drop x γ) (msyn1 ρ) t
.
Proof.
  intros.
  split.
  - auto using drop_RG.
  - eapply drop_msubst.
    eassumption.
Qed.


Lemma drop_RG__msubst_2 k Γ γ γ' x Δ ρ:
  0 < k -> (* is this necessary?  *)
  RD Δ ρ ->
  RG ρ k Γ γ γ' ->
  forall t T,
    Δ ,, drop x Γ |-+ t : T ->
    RG ρ k (drop x  Γ) (drop x γ) (drop x γ') /\
    close γ' (msyn2 ρ) t = close (drop x γ') (msyn2 ρ) t
.
Admitted.

Lemma approx_drop Δ x Γ e e' T :
  Δ,, (drop x Γ) |- e ≤ e' : T ->
  Δ,, Γ |- e ≤ e' : T.
Proof.
  intros H_approx_drop.
  unfold LR_logically_approximate.
  split. admit. (* weakening *)
  split. admit. (* weakening *)
  intros k ρ γ γ' RD RG.
  unfold LR_logically_approximate in H_approx_drop.
  destruct_hypos.
  specialize (H1 k ρ (drop x γ) (drop x γ') RD).
  assert (H_gt : 0 < k) by admit.
  specialize (drop_RG__msubst_1 _ _ _ _ _ _ _ H_gt RD RG e T H) as [H_RG' H_subst].
  specialize (drop_RG__msubst_2 _ _ _ _ _ _ _ H_gt RD RG e' T H0) as [_ H_subst'].
  apply H1 in H_RG'.
  rewrite H_subst, H_subst'.
  assumption.
Admitted.


Lemma compatibility_TyAbs: forall Δ Γ bX K T e e',
    LR_logically_approximate ((bX, K) :: Δ) (drop_ty_var bX Γ) e e' T ->
    LR_logically_approximate Δ Γ (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof with eauto_LR.
  intros Δ Γ bX K T e e' IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... 
  split...

  intros k rho γ γ' HRD HRG.

  autorewrite with RC.

  rewrite msubstA_TyAbs. rewrite msubstA_TyAbs.
  rewrite msubst_TyAbs. rewrite msubst_TyAbs.
  rewrite msubstT_TyForall. rewrite msubstT_TyForall.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  eexists. eexists.

  split. {
    eapply eval_result. apply R_Value. apply V_TyAbs.
  }

  split... 
  (* BROKEN BY new tyabs rule! *)
  {
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

  apply drop_ty_var__RG with (bX := bX) in HRG as [γ_dropped [γ_dropped' H_RG']].
  assert (HRD' : RD ((bX, K) :: Δ) ((bX, (Chi, T1, T2)) :: rho)). {
    eauto using RD.
  }
  specialize (IH__e _ _ _ _ HRD' H_RG').
  (*
  eapply IH__e.
  - eapply RD_cons; eauto.
  - apply RG_extend_rho.
    eapply RG_monotone; eauto.
    rewrite Nat.sub_0_r in Hlt_i.
    assert (H_ : inclusion γ_dropped γ /\ inclusion γ_dropped' γ').


    (* apply Nat.lt_le_incl.
    assumption. *)
    *)
Admitted.
