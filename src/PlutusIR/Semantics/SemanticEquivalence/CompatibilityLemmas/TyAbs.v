Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.

Search "RC".

(* TODO: Not sure if this holds *)
Lemma RC_rename_T k T rhos ρ e e' bX bY :
    RC k T                                ((bX, ρ)::rhos) e e' ->
    RC k (substituteTCA bX (Ty_Var bY) T) ((bY, ρ)::rhos) e e'.
Proof.
Admitted.

Lemma compatibility_TyAbs: forall Delta Gamma bX bY K T e e',
    LR_logically_approximate ((bX, K) :: Delta) (drop_ty_var bX (drop_ty_var bY Gamma)) e e' T ->
        LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') 
                (Ty_Forall bY K (substituteTCA bX (Ty_Var bY) T)).
Proof with eauto_LR.
  intros Delta Gamma bX bY K T e e' IH_LR.
  unfold LR_logically_approximate.
  
  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... 
  split...

  intros k rho env env' HRD HRG.

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

  eexists. eexists. eexists. eexists.

  split... split...

  intros.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite substA_msubst by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.
  rewrite <- substA_msubstA by eauto using Ty.kindable_empty__closed.

  assert (close env (msyn1 rho) (substA bX T1 e) 
    = close env (msyn1 ((bX, (Chi, T1, T2))::rho)) e) by auto.
  assert (close env' (msyn2 rho) (substA bX T2 e') = 
    close env' (msyn2 ((bX, (Chi, T1, T2))::rho)) e') by auto.
  rewrite H2.
  rewrite H3.
  (* ADMIT: bX vs bY. T is related to e/e' with bX*)

  assert (RC i T ((bX, (Chi, T1, T2))::rho) (close env (msyn1 ((bX, (Chi, T1, T2))::rho)) e)
    (close env' (msyn2 ((bX, (Chi, T1, T2))::rho)) e')).
  {
    eapply IH__e.
    - eapply RD_cons; eauto.
    - apply RG_extend_rho.
      eapply RG_monotone; eauto.
      (*
      ADMIT: I think same as TyAbs issue 16 branch, see for solution after
        having merged PR80
             
      rewrite <- minus_n_O in Hlt__j.
      apply Nat.lt_le_incl.
      assumption. *)
      admit.
  }

  apply RC_rename_T; assumption.  

Admitted.