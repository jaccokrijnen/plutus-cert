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

Lemma drop_RG k Γ γ γ' x :
  0 < k ->
  RG [] k Γ γ γ' ->
  RG [] k (drop x Γ) (drop x γ) (drop x γ')
.
Proof.
  induction 2; simpl.
  - constructor.
  - destruct (x0 =? x);
    eauto using RG.
Qed.
(*
Lemma drop_RG_msubst k Γ γ γ' x :
  0 < k ->
  RG [] k Γ γ γ' ->
    (forall t T, [] ,, drop x Γ |-+ t : T -> msubst γ t = msubst (drop x γ) t) /\
    (forall t T, [] ,, drop x Γ |-+ t : T -> msubst γ' t = msubst (drop x γ') t)
.
Proof.
  intros H_k.
  induction 1.
  - simpl. split; constructor.
  - rewrite drop_equation.
    simpl.
    destruct (x0 =? x) eqn:Heq.
    + (* x0 = x *)
      apply eqb_eq in Heq. subst x0.
      destruct_hypos.
      split.
      * eauto.
      * split.
        ** intros t T' H_ty.
           specialize (H4 _ _ H_ty).
           simpl.
           rewrite <- H4.
           assert (H_id : subst x v1 t = t) by admit. (* x not free in t *)
           rewrite H_id. reflexivity.
        ** intros t T' H_ty.
           specialize (H5 _ _ H_ty).
           simpl.
           rewrite <- H5.
           assert (H_id : subst x v2 t = t) by admit. (* x not free in t *)
           rewrite H_id. reflexivity.
    + (* x0 /= x *)
      destruct_hypos.
      eexists. eexists.
      split.
      * constructor; eauto.
      * split.
        ** intros t T' H_ty.
           simpl.
           eapply H4.
           apply RV_typable_empty_1 in H.
           destruct_hypos.
           simpl in *.
           eapply substitution_preserves_typing__Term.
           *** eassumption.
           *** eauto.
           *** eauto.
           *** eauto.
        ** intros t T' H_ty.
           simpl.
           eapply H5.
           apply RV_typable_empty_2 in H.
           destruct_hypos.
           simpl in *.
           eapply substitution_preserves_typing__Term.
           *** eassumption.
           *** eauto.
           *** eauto.
           *** eauto.
Admitted.
*)

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
  assert (H_ty1 :
    exists Tn, normalise (msubstT (msyn1 ρ) T) Tn /\
      ([] ,, drop x Γ |-+ (msubstA (msyn1 ρ) e) : Tn)) by admit.
  assert (H_ty2 :
    exists Tn, normalise (msubstT (msyn2 ρ) T) Tn /\
      ([] ,, drop x Γ |-+ (msubstA (msyn2 ρ) e') : Tn)) by admit.
Admitted.


Lemma compatibility_TyAbs: forall Delta Gamma bX K T e e',
    LR_logically_approximate ((bX, K) :: Delta) (drop_ty_var bX Gamma) e e' T ->
    LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof with eauto_LR.
  intros Delta Gamma bX K T e e' IH_LR.
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
  assert (HRD' : RD ((bX, K) :: Delta) ((bX, (Chi, T1, T2)) :: rho)). {
    eauto using RD.
  }
  (*
  specialize (IH__e _ _ _ _ HRD' H_RG').
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
