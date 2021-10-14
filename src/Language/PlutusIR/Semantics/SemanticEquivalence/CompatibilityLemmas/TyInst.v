Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.


Lemma msubst_TyInst : forall ss t0 T0,
    msubst_term ss (TyInst t0 T0) = TyInst (msubst_term ss t0) T0.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma msubstA_TyInst : forall ss t0 T0,
    msubstA_term ss (TyInst t0 T0) = TyInst (msubstA_term ss t0) (msubstT ss T0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma compatibility_TyInst: forall Delta Gamma e e' bX K T T' S T1,
    Delta |-* T1 : K ->
    substituteTCA bX T1 T T' ->
    normalise T' S ->
    LR_logically_approximate Delta Gamma e e' (Ty_Forall bX K T) ->
    LR_logically_approximate Delta Gamma (TyInst e T1) (TyInst e' T1) S.
Proof with eauto_LR.
  intros Delta Gamma e e' bX K T T' S T1 Hkind__T1 Hstca__T' Hnorm IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split... 

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_TyInst. rewrite msubstA_TyInst.
  rewrite msubst_TyInst. rewrite msubst_TyInst.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f.
  + subst.
    apply skip.
  + subst.

    rename j1 into j_1.
    rename j0 into j_0.

    assert (HRC :
      RC k (Ty_Forall bX K T) rho
        (msubst_term env (msubstA_term (msyn1 rho) e))
        (msubst_term env' (msubstA_term (msyn2 rho) e'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := TyAbs X K0 t0) in HRC as temp...
    destruct temp as [e'_f [j'_1 [Hev__e'_f HRV]]].

    apply RV_instantiational_extensionality in HRV as temp...
    destruct temp as [e_body [e'_body [Heq [Heq' Hie]]]].

    inversion Heq. subst.

    eexists. eexists.

    split. eapply E_TyInst...
Admitted.