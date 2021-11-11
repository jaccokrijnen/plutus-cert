Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.

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
  

Lemma compatibility_IWrap : forall Delta Gamma e e' T K Tn F Fn T0n,
    Delta |-* T : K ->
    normalise T Tn ->
    Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
    normalise F Fn ->
    normalise (unwrapIFix Fn K Tn) T0n ->
    LR_logically_approximate Delta Gamma e e' T0n ->
    LR_logically_approximate Delta Gamma (IWrap F T e) (IWrap F T e') (Ty_IFix Fn Tn).
Proof with eauto_LR.
  intros Delta Gamma e e' T K Tn F Fn T0n.
  intros Hkind__T Hnorm__Tn Hkind__F Hnorm__F Hnorm__T0n IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH]].

  split... split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_IWrap. rewrite msubstA_IWrap.
  rewrite msubst_IWrap. rewrite msubst_IWrap.
  
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f; subst.
  - rename v0 into e_f. 

    assert (HRC : 
      RC k T0n rho 
        (msubst_term env (msubstA_term (msyn1 rho) e)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e'))
    )... 

    apply RC_to_RV with (j := j) (e_f := e_f) in HRC as temp...
    destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

    eexists. eexists.
    split. eapply E_IWrap... eapply RV_error in HRV... destruct HRV as [ [Hnerr Hnerr'] | [Herr Herr']]...

    split... {
      rewrite msubstT_IFix.
      eapply preservation in Hkind__T as H...
      eapply preservation in Hkind__F as H0...
      eapply msubstT_preserves_kinding_1 in H as H1...
      eapply msubstT_preserves_kinding_1 in H0 as H2...
      eapply strong_normalisation in H1 as H3...
      eapply strong_normalisation in H2 as H6...
      destruct H3. destruct H6.
      eexists.
      split. eapply N_TyIFix...
      eapply T_IWrap...
      - eapply msubstT_preserves_kinding_1...
      - admit.
      - eapply msubstT_preserves_kinding_1...
      - admit.
      - admit.
      - admit. 
    } 
    split... {
      rewrite msubstT_IFix.
      eapply preservation in Hkind__T as H...
      eapply preservation in Hkind__F as H0...
      eapply msubstT_preserves_kinding_2 in H as H1...
      eapply msubstT_preserves_kinding_2 in H0 as H2...
      eapply strong_normalisation in H1 as H3...
      eapply strong_normalisation in H2 as H6...
      destruct H3. destruct H6.
      eexists.
      split. eapply N_TyIFix...
      eapply T_IWrap...
      - eapply msubstT_preserves_kinding_2...
      - admit.
      - eapply msubstT_preserves_kinding_2...
      - admit.
      - admit.
      - admit. 
    }

    left. 
    split. intros Hcon. inversion Hcon.
    split. intros Hcon. inversion Hcon.

    eexists. eexists. eexists. eexists.
    split... split... split... split...

    intros.

    assert (K0 = K). {
      eapply preservation in Hkind__T...
      eapply msubstT_preserves_kinding_2 in Hkind__T...
      eapply unique_kinds...
    }
    subst.
    eapply normalisation__deterministic in Hnorm__T0n...
    subst.

    eapply RV_to_RC.

    eapply RV_monotone...
  - (* E_Error_Iwrap *)
    assert (HRC : 
      RC k T0n rho 
        (msubst_term env (msubstA_term (msyn1 rho) e)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e'))
    )... 

    apply RC_to_RV with (j := j0) (e_f := Error T') in HRC as temp...
    destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

    eapply RV_error in HRV as temp...

    destruct temp as [ [Hnerr Hnerr'] | [Herr Herr']]...
    + exfalso... eapply Hnerr... econstructor.
    + inversion Herr'. subst.
      eexists. eexists.
      split... eapply E_Error_IWrap...
      
      split. {
        rewrite msubstT_IFix.
        eapply preservation in Hkind__T as H...
        eapply preservation in Hkind__F as H0...
        eapply msubstT_preserves_kinding_1 in H as H1...
        eapply msubstT_preserves_kinding_1 in H0 as H2...
        eapply strong_normalisation in H1 as H3...
        eapply strong_normalisation in H2 as H6...
        destruct H3. destruct H6.
        eexists.
        split. eapply N_TyIFix...
        eapply T_Error.
        eapply K_IFix.
        eapply H1.
        eapply H2.
        eapply N_TyIFix...
      }

      split. {
        rewrite msubstT_IFix.
        eapply preservation in Hkind__T as H...
        eapply preservation in Hkind__F as H0...
        eapply msubstT_preserves_kinding_2 in H as H1...
        eapply msubstT_preserves_kinding_2 in H0 as H2...
        eapply strong_normalisation in H1 as H3...
        eapply strong_normalisation in H2 as H6...
        destruct H3. destruct H6.
        eexists.
        split. eapply N_TyIFix...
        eapply T_Error.
        eapply K_IFix.
        eapply H1.
        eapply H2.
        eapply N_TyIFix...
      }
      right...
Admitted.