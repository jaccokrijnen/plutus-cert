Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.

Require Import Arith.

Lemma msubst_Unwrap : forall ss M,
    msubst_term ss (Unwrap M) = Unwrap (msubst_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_Unwrap : forall ss M ,
    msubstA_term ss (Unwrap M) = Unwrap (msubstA_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma compatibility_Unwrap : forall Delta Gamma e e' Fn Tn K T0n,
    Delta |-* Tn : K ->
    normalise (unwrapIFix Fn K Tn) T0n ->
    LR_logically_approximate Delta Gamma e e' (Ty_IFix Fn Tn)->
    LR_logically_approximate Delta Gamma (Unwrap e) (Unwrap e') T0n.
Proof with eauto_LR.
  intros Delta Gamma e e' Fn Tn K T0n.
  intros Hkind__Tn Hnorm__T0n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split...

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Unwrap. rewrite msubstA_Unwrap.
  rewrite msubst_Unwrap. rewrite msubst_Unwrap.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f; subst.
  - rename j0 into j_1.
    rename H0 into Hev'__e_f.

    assert (HRC : 
      RC k (Ty_IFix Fn Tn) rho
        (msubst_term env (msubstA_term (msyn1 rho) e))
        (msubst_term env' (msubstA_term (msyn2 rho) e'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := IWrap F T e_f) in HRC as temp...
    destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

    apply RV_unwrap in HRV as temp...
    destruct temp as [temp | temp].
    + destruct temp as [Hnerr [Hnerr' temp]].
      destruct temp as [v_2 [v'_2 [F0 [F0' [T0 [T0' [Heq [Heq' Hunwr]]]]]]]].
      inversion Heq. subst.

      eexists. eexists.
      split. eapply E_Unwrap...

      split... {
        (* ADMIT: I had no time to finish this, but should hold.*)
        admit.
      }
      split... {
        (* ADMIT: I had no time to finish this, but should hold. *)
        admit.
      }

      eapply RV_condition...
      eapply RV_unfolded_to_RV.
      split. eapply eval_to_value in Hev'__e_f. inversion Hev'__e_f. subst. assumption. inversion H. 
      split. eapply eval_to_value in Hev__e'_f. inversion Hev__e'_f. subst. assumption. inversion H.
      eapply Hunwr...

      eapply msubstT_preserves_kinding_1...
      eapply msubstT_preserves_kinding_2...
    + (* ADMIT: Both evaluate to errors, should hold. *)
      admit.
  - (* ADMIT: I had no time to finish this. *)
    admit.
(* ADMIT: Proof contains admits. *) 
Admitted.