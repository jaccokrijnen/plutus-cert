Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.IWrap.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.

Lemma normalise_unwrapIFix_commutes'_1 : forall ck rho Fn K Tn T0n Fn' Tn' T0n',
    RD ck rho ->
    normalise (unwrapIFixFresh Fn K Tn) T0n ->
    normalise (msubstT (msyn1 rho) Fn) Fn' ->
    normalise (msubstT (msyn1 rho) Tn) Tn' ->
    normalise (unwrapIFixFresh Fn' K Tn') T0n' ->
    normalise (msubstT (msyn1 rho) T0n) T0n'.
Proof.
(* ADMIT: Commutativity should hold. *)
Admitted.

Lemma normalise_unwrapIFix_commutes'_2 : forall ck rho Fn K Tn T0n Fn' Tn' T0n',
    RD ck rho ->
    normalise (unwrapIFixFresh Fn K Tn) T0n ->
    normalise (msubstT (msyn2 rho) Fn) Fn' ->
    normalise (msubstT (msyn2 rho) Tn) Tn' ->
    normalise (unwrapIFixFresh Fn' K Tn') T0n' ->
    normalise (msubstT (msyn2 rho) T0n) T0n'.
Proof.
(* ADMIT: Commutativity should hold. *)
Admitted.

Lemma compatibility_Unwrap : forall Delta Gamma e e' Fn Tn K T0n,
    Delta |-* Tn : K ->
    normalise (unwrapIFixFresh Fn K Tn) T0n ->
    LR_logically_approximate Delta Gamma e e' (Ty_IFix Fn Tn)->
    LR_logically_approximate Delta Gamma (Unwrap e) (Unwrap e') T0n.
Proof with eauto_LR.
  intros Delta Gamma e e' Fn Tn K T0n.
  intros Hkind__Tn Hnorm__T0n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].
  (* TODO: What did I break here by adding kinding assumptions??? *)
  (* split... split...

  intros k rho env env' HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Unwrap. rewrite msubstA_Unwrap.
  rewrite msubst_Unwrap. rewrite msubst_Unwrap.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f; subst.
  - rename j1 into j_1.
    rename H1 into Hev'__e_f.

    assert (HRC :
      RC k (Ty_IFix Fn Tn) rho
        (msubst env (msubstA (msyn1 rho) e))
        (msubst env' (msubstA (msyn2 rho) e'))
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
        eapply RV_typable_empty_1 in HRV as temp...
        destruct temp as [T_ih [Hnorm__T_ih Htyp__ih]].
        rewrite msubstT_IFix in Hnorm__T_ih.
        inversion Hnorm__T_ih. subst.
        inversion Htyp__ih. subst.

        eexists. split...
        eapply normalise_unwrapIFix_commutes'_1...
        eapply preservation in H9...
        eapply closing_preserves_kinding_1 in Hkind__Tn...
        eapply preservation in Hkind__Tn...
        eapply unique_kinds in H9... subst...
      }
      split... {
        eapply RV_typable_empty_2 in HRV as temp...
        destruct temp as [T_ih [Hnorm__T_ih Htyp__ih]].
        rewrite msubstT_IFix in Hnorm__T_ih.
        inversion Hnorm__T_ih. subst.
        inversion Htyp__ih. subst.

        eexists. split...
        eapply normalise_unwrapIFix_commutes'_2...
        eapply preservation in H9...
        eapply closing_preserves_kinding_2 in Hkind__Tn...
        eapply preservation in Hkind__Tn...
        eapply unique_kinds in H9... subst...
      }

      eapply RV_condition...
      eapply RV_unfolded_to_RV.
      split. eapply eval_to_result in Hev'__e_f. inversion Hev'__e_f. apply <- result__IWrap. eassumption.
      split. eapply eval_to_result in Hev__e'_f. inversion Hev__e'_f. apply <- result__IWrap. eassumption.
      eapply Hunwr...

      eapply closing_preserves_kinding_1...
      eapply closing_preserves_kinding_2...
    + destruct temp as [Herr Herr'].
      inversion Herr.
  - rename j1 into j_1.

    assert (HRC :
      RC k (Ty_IFix Fn Tn) rho
        (msubst env (msubstA (msyn1 rho) e))
        (msubst env' (msubstA (msyn2 rho) e'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := Error T) in HRC as temp...
    destruct temp as [e'_f [j'_1 [Hev__e'_f HRV]]].
    apply RV_error in HRV as temp...
    destruct temp as [temp | temp].
    + destruct temp.
      exfalso.
      apply H.
      econstructor.
    + destruct temp.
      inversion H. subst.

      eexists. eexists.
      split. admit. (* eapply E_Error_Unwrap... *)

      split... admit. (* ADMIT: I had no time to finish this. Should hold. *)
      split... admit. (* ADMIT: I had no time to finish this. Should hold. *)
ADMIT: Proof contains admits. *)
Admitted.
