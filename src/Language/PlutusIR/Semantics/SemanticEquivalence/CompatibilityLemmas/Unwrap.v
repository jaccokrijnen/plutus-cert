Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.

Lemma msubst_Unwrap : forall ss M,
    msubst_term ss (Unwrap M) = Unwrap (msubst_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_Unwrap : forall ss M ,
    msubstA_term ss (Unwrap M) = Unwrap (msubstA_term ss M).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.


Lemma compatibility_Unwrap : forall Delta Gamma F T e e' K S,
    Delta |-* T : K ->
    normalise (unwrapIFix F K T) S ->
    LR_logically_approximate Delta Gamma e e' (Ty_IFix F T)->
    LR_logically_approximate Delta Gamma (Unwrap e) (Unwrap e') S.
Proof with eauto_LR.
  intros Delta Gamma F T e e' K S Hkind__T Hnorm IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split...

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Unwrap. rewrite msubstA_Unwrap.
  rewrite msubst_Unwrap. rewrite msubst_Unwrap.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.
  rename j0 into j_1.
  rename H0 into Hev'__e_f.

  assert (HRC : 
    RC k (Ty_IFix F T) rho
      (msubst_term env (msubstA_term (msyn1 rho) e))
      (msubst_term env' (msubstA_term (msyn2 rho) e'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := IWrap F0 T0 e_f) in HRC as temp...
  destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

  apply RV_unwrap in HRV as temp...
  destruct temp as [v_2 [v'_2 [Heq [Heq' Hunwr]]]].
  inversion Heq. subst.

  eexists. eexists.
  split. eapply E_Unwrap...

  split... apply skip.
  split... apply skip.

  eapply RV_condition...
  eapply RV_unfolded_to_RV.
  split. eapply eval_to_value in Hev'__e_f. inversion Hev'__e_f. subst. assumption.
  split. eapply eval_to_value in Hev__e'_f. inversion Hev__e'_f. subst. assumption.  
  eapply Hunwr...

  apply skip.
Qed.