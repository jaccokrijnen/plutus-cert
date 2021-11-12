Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.

Require Import Arith.


Lemma msubst_TyInst : forall ss t0 T0,
    msubst_term ss (TyInst t0 T0) = TyInst (msubst_term ss t0) T0.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubstA_TyInst : forall ss t0 T0,
    msubstA_term ss (TyInst t0 T0) = TyInst (msubstA_term ss t0) (msubstT ss T0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.



Lemma compatibility_TyInst: forall Delta Gamma e e' X K2 T1n T2 T2n T0n,
    Delta |-* T2 : K2 ->
    normalise T2 T2n ->
    normalise (substituteTCA X T2n T1n) T0n ->
    LR_logically_approximate Delta Gamma e e' (Ty_Forall X K2 T1n) ->
    LR_logically_approximate Delta Gamma (TyInst e T2) (TyInst e' T2) T0n.
Proof with eauto_LR.
  intros Delta Gamma e e' X K2 T1n T2 T2n T0n.
  intros Hkind__T2 Hnorm__T2n Hnorm__T0n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split... 

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_TyInst. rewrite msubstA_TyInst.
  rewrite msubst_TyInst. rewrite msubst_TyInst.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. all: subst.
  - (* E_TyInst *)
    rename j1 into j_1.
    rename j0 into j_0.

    assert (HRC :
      RC k (Ty_Forall X K2 T1n) rho
        (msubst_term env (msubstA_term (msyn1 rho) e))
        (msubst_term env' (msubstA_term (msyn2 rho) e'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := TyAbs X0 K t0) in HRC as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV]]].

    apply RV_instantiational_extensionality in HRV as temp...
    destruct temp as [temp | temp].
    + destruct temp as [Hnerr [Hnerr' [e_body [e'_body [Heq [Heq' Hie]]]]]].

      inversion Heq. subst. clear Heq.

      eapply msubstT_preserves_kinding_1 in Hkind__T2 as H10...
      eapply msubstT_preserves_kinding_2 in Hkind__T2 as H11...
      remember (fun k t t' => RV k T2 rho t t') as Chi.
      assert (Rel (msubstT (msyn1 rho) T2) (msubstT (msyn2 rho) T2) Chi). {
        subst.
        eapply validity...
      }
      remember (Hie (msubstT (msyn1 rho) T2) (msubstT (msyn2 rho) T2) Chi H10 H11 H).
      assert (HRC2 :
        RC (k - j_1 - 1)
          T1n
          ((X, (Chi, msubstT (msyn1 rho) T2, msubstT (msyn2 rho) T2)) :: rho)%list
          <{ [[{msubstT (msyn1 rho) T2} / X] e_body }>
          <{ [[{msubstT (msyn2 rho) T2} / X] e'_body }>  
      ). eapply r...

      eapply RC_to_RV with (j := j_0) (e_f := e_f) in HRC2 as temp...
      destruct temp as [e'_f [j'_0 [Hev__e'_f HRV2]]].


      eexists. eexists.
      split. eapply E_TyInst...

      split. admit.
      split. admit.

      eapply RV_condition...
      eapply RV_equiv...
Admitted.