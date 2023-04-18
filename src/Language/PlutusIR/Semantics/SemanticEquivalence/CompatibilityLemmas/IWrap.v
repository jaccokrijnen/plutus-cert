Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.

Lemma normalise_msubstT_commutes_1 : forall T Tn Tn' ck rho K,
    RD ck rho ->
    mupdate empty ck |-* T : K ->
    normalise T Tn ->
    normalise (msubstT (msyn1 rho) Tn) Tn' ->
    normalise (msubstT (msyn1 rho) T) Tn'.
Proof. 
(* ADMIT: Commutativity should hold. *)
Admitted.

Lemma normalise_msubstT_commutes_2 : forall T Tn Tn' ck rho K,
    RD ck rho ->
    mupdate empty ck |-* T : K ->
    normalise T Tn ->
    normalise (msubstT (msyn2 rho) Tn) Tn' ->
    normalise (msubstT (msyn2 rho) T) Tn'.
Proof. 
(* ADMIT: Commutativity should hold. *)
Admitted.

Lemma normalise_unwrapIFix_commutes_1 : forall ck rho Fn K Tn T0n Fn' Tn' T0n',
    RD ck rho ->
    normalise (unwrapIFix Fn K Tn) T0n ->
    normalise (msubstT (msyn1 rho) Fn) Fn' ->
    normalise (msubstT (msyn1 rho) Tn) Tn' ->
    normalise (msubstT (msyn1 rho) T0n) T0n' ->
    normalise (unwrapIFix Fn' K Tn') T0n'.
Proof.
(* ADMIT: Commutativity should hold. Well-typedness of unwrapIFix term
   should follow from uniqueness property. *)
Admitted.

Lemma normalise_unwrapIFix_commutes_2 : forall ck rho Fn K Tn T0n Fn' Tn' T0n',
    RD ck rho ->
    normalise (unwrapIFix Fn K Tn) T0n ->
    normalise (msubstT (msyn2 rho) Fn) Fn' ->
    normalise (msubstT (msyn2 rho) Tn) Tn' ->
    normalise (msubstT (msyn2 rho) T0n) T0n' ->
    normalise (unwrapIFix Fn' K Tn') T0n'.
Proof.
(* ADMIT: Commutativity should hold. Well-typedness of unwrapIFix term
   should follow from uniqueness property. *)
Admitted.

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
      eapply RV_typable_empty_1 in HRV as temp...
      destruct temp as [T0n' [Hnorm__T0n' Htyp__e_f]].
      eapply T_IWrap...
      - eapply msubstT_preserves_kinding_1...
      - eapply normalise_msubstT_commutes_1...
      - eapply msubstT_preserves_kinding_1...
      - eapply normalise_msubstT_commutes_1...
      - eapply normalise_unwrapIFix_commutes_1...
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
      eapply RV_typable_empty_2 in HRV as temp...
      destruct temp as [T0n' [Hnorm__T0n' Htyp__e'_f]].
      eapply T_IWrap...
      - eapply msubstT_preserves_kinding_2...
      - eapply normalise_msubstT_commutes_2...
      - eapply msubstT_preserves_kinding_2...
      - eapply normalise_msubstT_commutes_2...
      - eapply normalise_unwrapIFix_commutes_2...
    }

    left. 
    split. intros Hcon. inversion Hcon.
    split. intros Hcon. inversion Hcon.

    eexists. eexists. eexists. eexists. eexists. eexists.
    split... split...
    
    intros.

    assert (K0 = K). {
      eapply preservation in Hkind__T...
      eapply msubstT_preserves_kinding_2 in Hkind__T...
      eapply unique_kinds...
    }
    subst.
    eapply normalisation__deterministic in Hnorm__T0n...
    subst.

    eapply RV_to_RC_trivial.

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
Qed.
