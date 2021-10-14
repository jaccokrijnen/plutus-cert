Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.

Lemma msubst_IWrap : forall ss F T M,
    msubst_term ss (IWrap F T M) = IWrap F T (msubst_term ss M).
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma msubstA_IWrap : forall ss F T M,
    msubstA_term ss (IWrap F T M) = IWrap (msubstT ss F) (msubstT ss T) (msubstA_term ss M).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed. 

Lemma msubstT_IFix : forall ss F T,
    msubstT ss (Ty_IFix F T) = Ty_IFix (msubstT ss F) (msubstT ss T).
Proof.
  induction ss; intros.
    - reflexivity.
    - destruct a. eauto.
Qed. 
  

Lemma compatibility_IWrap : forall Delta Gamma F T e e' K S,
    Delta |-* T : K ->
    Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
    normalise (unwrapIFix F K T) S ->
    LR_logically_approximate Delta Gamma e e' S ->
    LR_logically_approximate Delta Gamma (IWrap F T e) (IWrap F T e') (Ty_IFix F T).
Proof with eauto_LR.
  intros Delta Gamma F T e e' K S Hkind__T Hkind__F Hnorm IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_IWrap. rewrite msubstA_IWrap.
  rewrite msubst_IWrap. rewrite msubst_IWrap.
  rewrite msubstT_IFix. rewrite msubstT_IFix.
  
  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.

  rename v0 into e_f. 

  assert (HRC : 
    RC k S rho 
      (msubst_term env (msubstA_term (msyn1 rho) e)) 
      (msubst_term env' (msubstA_term (msyn2 rho) e'))
  )... 

  apply RC_to_RV with (j := j) (e_f := e_f) in HRC as temp...
  destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

  eexists. eexists.
  split. eapply E_IWrap...

  split... apply skip.
  split... apply skip.
  

  eexists. eexists.
  split...
  split...

  intros.

  assert (K0 = K) by apply skip. (* TODO *)
  subst.
  assert (S0 = S) by apply skip. (* TODO *)
  subst.

  eapply RV_to_RC.

  eapply RV_monotone.
  + eapply H_RD.
  + eapply HRV. 
  + eauto_LR.
Qed.