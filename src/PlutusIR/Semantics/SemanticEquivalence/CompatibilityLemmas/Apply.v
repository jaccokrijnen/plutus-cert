Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

From Coq Require Import Lia.
From Coq Require Import Arith.
From Coq Require Import List.
Import ListNotations.

Lemma compatibility_Apply : forall Delta Gamma e1 e2 e1' e2' T1n T2n,
    LR_logically_approximate Delta Gamma e1 e1' (Ty_Fun T1n T2n) ->
    LR_logically_approximate Delta Gamma e2 e2' T1n ->
    LR_logically_approximate Delta Gamma (Apply e1 e2) (Apply e1' e2') T2n.
Proof with eauto_LR.
  intros Delta Gamma e1 e2 e1' e2' T1 T2 IH_LR1 IH_LR2.
  unfold LR_logically_approximate.

  destruct IH_LR1 as [Htyp__e1 [Htyp__e1' IH1]].
  destruct IH_LR2 as [Htyp__e2 [Htyp__e2' IH2]].

  split...
  split...

  intros k rho env env' H_RD H_RG.
  subst.

  autorewrite with RC.
  
  rewrite msubstA_Apply. rewrite msubstA_Apply. 
  rewrite msubst_Apply. rewrite msubst_Apply.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f; subst.
  - (* E_Apply *)
    rename v2 into e_f2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j0 into j_3.

    assert (HRC1 : 
      RC k (Ty_Fun T1 T2) rho 
        (msubst_term env (msubstA_term (msyn1 rho) e1)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e1'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := LamAbs x T t0) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].

    assert (k - j_1 <= k)...
    assert (HRC2 : 
      RC (k - j_1) T1 rho 
        (msubst_term env (msubstA_term (msyn1 rho) e2)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e2'))
    ) by eauto using RG_monotone.
    clear H.

    apply RC_to_RV  with (j := j_2) (e_f := e_f2) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_functional_extensionality in HRV1 as temp...

    destruct temp as [temp | temp].
    + destruct temp as [Hnerr [Hnerr' temp]]. 
      destruct temp as [x0 [e_body [e'_body [T1a [T1'a [Heq [Heq' Hfe]]]]]]].
      inversion Heq. subst. clear Heq.

      apply RV_monotone with (i := k - j_1 - j_2 - 1) (ck := Delta)  in HRV2...

      apply Hfe with (i := k - j_1 - j_2 - 1) in HRV2 as HRC0...

      assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
      rewrite H.
      clear H.

      apply RC_to_RV with (j := j_3) (e_f := e_f) in HRC0 as temp...
      destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

      eexists. eexists. 
      split. eapply E_Apply... apply RV_error in HRV2... destruct HRV2 as [ [Hnerr0 Hnerr0'] | [Herr0 Herr0']]...

      split. eapply RV_typable_empty_1...
      split. eapply RV_typable_empty_2...
      eapply RV_condition...

      assert (~ is_error e'_f2). {
        apply RV_error in HRV2.
        destruct HRV2.
          - destruct H. assumption.
          - destruct H. contradiction.
          - lia.
        }
      auto.
    + destruct temp as [Herr Herr'].
      inversion Herr.
  - (* E_NeutralApply *)
    (* ADMIT: See end of proof. *)
    admit.
  - (* E_NeutralApplyPartial *)
    (* ADMIT: See end of proof. *)
    admit.
  - (* E_NeutralApplyFull *)
    (* ADMIT: See end of proof. *)
    admit.
  - (* E_Error_Apply1 *)
    rename j1 into j_1.

    assert (HRC1 : 
      RC k (Ty_Fun T1 T2) rho 
        (msubst_term env (msubstA_term (msyn1 rho) e1)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e1'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := Error T) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].

    apply RV_condition in HRV1 as temp...
    destruct temp as [temp | temp].
    + destruct temp. exfalso. apply H. econstructor.
    + destruct temp.
      Set Diffs "on".
      inversion H0. subst.

      eexists. eexists.
      split. eapply E_Error_Apply1...

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_1 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      right...
      
  - (* E_Error_Apply2 *)
    rename j2 into j_2.

    assert (HRC2 : 
      RC k T1 rho 
        (msubst_term env (msubstA_term (msyn1 rho) e2)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e2'))
    ) by eauto using RG_monotone.

    apply RC_to_RV  with (j := j_2) (e_f := Error T) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_condition in HRV2 as temp...
    destruct temp as [temp | temp].
    + destruct temp. exfalso. apply H. econstructor.
    + destruct temp.
      inversion H0. subst.

      eexists. eexists.
      split. eapply E_Error_Apply2...

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_1 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      right...
(* ADMIT: We do not handle built-in functions yet. *)
Admitted.
