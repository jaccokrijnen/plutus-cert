Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import PlutusCert.Util.

Require Import Coq.Lists.List.

Local Open Scope list_scope.



Lemma mupdate_flatten : forall {X : Type} (m : partial_map X) x l,
    mupdate m (flatten (x :: l)) = mupdate (mupdate m x) (flatten l).
Proof.
  intros.
  unfold flatten.
  simpl.
  rewrite List.concat_app.
  simpl.
  rewrite List.app_nil_r.
  rewrite <- mupdate_app.
  reflexivity.
Qed.

Lemma map_normalise__app' : forall l1 l1n l2 l2n,
    map_normalise l1 l1n ->
    map_normalise l2 l2n ->
    map_normalise (l1 ++ l2) (l1n ++ l2n).
Proof.
  induction l1; intros.
  - inversion H. subst. simpl. eauto.
  - inversion H. subst. simpl. econstructor. eauto. eauto.
Qed.


Lemma compatibility_TermBind : forall Delta Gamma stricty x Tb Tbn tb tb' b b' bs bs' t t' Tn,
    Delta |-* Tb : Kind_Base ->
    normalise Tb Tbn ->
    forall Delta_ih Gamma_ih bsGn,
      b = TermBind stricty (VarDecl x Tb) tb ->
      b' = TermBind stricty (VarDecl x Tb) tb' ->
      Delta_ih = mupdate Delta (binds_Delta b) ->
      map_normalise (binds_Gamma b) bsGn ->
      Gamma_ih = mupdate Gamma bsGn ->
      LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (Let NonRec bs' t') Tn ->
      LR_logically_approximate Delta Gamma tb tb' Tbn ->
      LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn.
Proof with eauto_LR.
  intros Delta Gamma stricty x Tb Tbn tb tb' b b' bs bs' t t' Tn.
  intros Hkind__Tb Hnorm__Tbn.
  intros Delta_ih Gamma_ih bsGn.
  intros Heq__b Heq__b' Heq__Delta_ih Hmapnorm__bsGn Heq__Gamma_ih IHLR__ih IHLR__tb.

  subst.

  destruct IHLR__ih as [Htyp__ih [Htyp__ih' IH__ih]].
  destruct IHLR__tb as [Htyp__tb [Htyp__tb' IH__tb]].

  split. {
    inversion Htyp__ih. subst.
    rewrite <- mupdate_flatten in H7.

    eapply T_Let...
    - unfold flatten.
      simpl.
      simpl in Hmapnorm__bsGn.
      rewrite List.concat_app.
      eapply map_normalise__app'...
    - rewrite mupdate_app. eapply H7.
  }

  split. {
    inversion Htyp__ih'. subst.
    rewrite <- mupdate_flatten in H7.

    eapply T_Let...
    - unfold flatten.
      simpl.
      simpl in Hmapnorm__bsGn.
      rewrite List.concat_app.
      eapply map_normalise__app'...
    - rewrite mupdate_app. eapply H7.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.
  
  rewrite msubstA_LetNonRec.
  rewrite msubstA_BindingsNonRec_cons.
  rewrite msubstA_TermBind.
  rewrite msubst_LetNonRec.
  rewrite msubst_BindingsNonRec_cons.
  rewrite msubst_TermBind.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  clear Hev__e_f. rename H3 into Hev__e_f.
  inversion Hev__e_f; subst.
  - (* E_Let_TermBind *)
    clear Hev__e_f.
    rename v1 into vb.
    rename j1 into jb.
    rename H7 into Hev__vb.
    rename H9 into Hev__e_f.

    assert (HRC__tb :
    RC k Tbn rho
      (msubst_term env (msubstA_term (msyn1 rho) tb))
      (msubst_term env' (msubstA_term (msyn2 rho) tb'))  
    )...
    clear IH__tb.

    eapply RC_to_RV with (j := jb) (e_f := vb) in HRC__tb as temp...
    destruct temp as [vb' [jb' [Hev__vb' HRV__vb]]].
    clear Hev__vb.
    clear HRC__tb.
  
    assert (HRC__ih :
      RC (k - jb - 1) Tn rho
        <{ /[ (x, vb) :: drop x env /] ( /[[ msyn1 rho /] {Let NonRec bs t} ) }>
        <{ /[ (x, vb') :: drop x env' /] ( /[[ msyn2 rho /] {Let NonRec bs' t'} ) }>
    ). {
      apply IH__ih with (ct0 := (x, Tbn) :: drop x ct) (ck0 := ck).
      - reflexivity.
      - inversion Hmapnorm__bsGn. subst.
        inversion H3. subst.
        simpl.
        eapply normalisation__deterministic in Hnorm__Tbn...
        subst.
        apply mupdate_drop.
      - assumption.
      - assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        replace vb with (msubstA_term (msyn1 rho) vb) by (eapply msubstA_closed; eauto).
        replace vb' with (msubstA_term (msyn2 rho) vb') by (eapply msubstA_closed; eauto).
        apply RG_cons.
        + apply RV_monotone with (k := k - jb) (ck := ck)...
          rewrite msubstA_closed...
          rewrite msubstA_closed...
        + eapply normalise_to_normal...
        + apply not_is_error_msubstA.
          assumption.
        + apply RG_monotone with (k := k) (ck := ck)...
          apply RG_drop...
    }
    clear IH__ih.

    apply RC_to_RV with (j := j2) (e_f := e_f) in HRC__ih as temp...
    + destruct temp as [e'_f [j2' [Hev__e'_f HRV0]]].
      clear Hev__e_f.

      rewrite msubstA_LetNonRec.
      rewrite msubstA_BindingsNonRec_cons.
      rewrite msubstA_TermBind.
      rewrite msubst_LetNonRec.
      rewrite msubst_BindingsNonRec_cons.
      rewrite msubst_TermBind.
    
      rewrite msubstA_LetNonRec in Hev__e'_f.
      rewrite msubst_LetNonRec in Hev__e'_f.

      rewrite <- msubstA_bnr__bvbs in Hev__e'_f.

      inversion Hev__e'_f. subst.

      eexists. eexists.
      split. {
        apply E_Let.
        apply E_Let_TermBind with (v1 := vb') (j1 := jb') (v2 := e'_f) (j2 := j2')...
        1: {
          eapply RV_error in HRV__vb...
          destruct HRV__vb as [ [Hnerr Hnerr'] | [Herr Herr']]...
        }
        simpl.
        rewrite <- msubst_bnr__bound_vars.
        rewrite <- msubstA_bnr__bvbs.
        destruct (existsb (eqb x) (bvbs bs')) eqn:Hexb.
        - assert (closed vb). eapply RV_closed_1...
          assert (closed vb'). eapply RV_closed_2...
          apply RG_env_closed in HRG as Hclss...
          destruct Hclss as [Hcls__env Hcls__env'].
          rewrite <- subst_bnr__msubst_bnr'...
          replace (concat (map bvb <{ /[[ msyn2 rho /][bnr] bs' }>)) with
            (bvbs  <{ /[[ msyn2 rho /][bnr] bs' }>)...
          rewrite <- msubstA_bnr__bvbs.

          apply existsb_exists in Hexb.
          destruct Hexb as [y [HIn Heqb]].
          apply eqb_eq in Heqb as Heq.
          subst.
          rewrite In__mdrop in H3...
        - assert (closed vb). eapply RV_closed_1...
          assert (closed vb'). eapply RV_closed_2...
          apply RG_env_closed in HRG as Hclss...
          destruct Hclss as [Hcls__env Hcls__env'].
          rewrite <- subst_bnr__msubst_bnr'...
          replace (concat (map bvb <{ /[[ msyn2 rho /][bnr] bs' }>)) with
            (bvbs  <{ /[[ msyn2 rho /][bnr] bs' }>)...
          rewrite <- msubstA_bnr__bvbs.

          apply existsb_nexists in Hexb.
          rewrite not_In__mdrop in H3...
          + unfold btvbs. simpl.
            replace (concat (map btvb bs')) with (btvbs bs')...

            rewrite <- subst_msubst''...
            * eapply RG_env_closed.
              eapply RG_drop...
              eauto_LR.
            * intros Hcon.
              apply Hexb.
              exists x.
              rewrite eqb_refl.
              eauto.
          + intros Hcon.
            apply Hexb.
            exists x.
            rewrite eqb_refl.
            eauto.
      }

      split... eapply RV_typable_empty_1...
      split... eapply RV_typable_empty_2...
    
      eapply RV_condition...
      eapply RV_monotone...

    + rewrite msubstA_LetNonRec.
      rewrite msubst_LetNonRec. 
      apply E_Let.

      simpl.
      simpl in Hev__e_f.

      rewrite <- msubst_bnr__bound_vars in Hev__e_f.
      rewrite <- msubstA_bnr__bvbs in Hev__e_f.

      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb. {
        assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        apply RG_env_closed in HRG as Hclss...
        destruct Hclss as [Hcls__env Hcls__env'].
        rewrite <- subst_bnr__msubst_bnr' in Hev__e_f...
        replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
          (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev__e_f...
        
        unfold btvbs in Hev__e_f.
        simpl in Hev__e_f.
        rewrite <- msubstA_bnr__bvbs.
        rewrite <- msubstA_bnr__bvbs in Hev__e_f.

        apply existsb_exists in Hexb.
        destruct Hexb as [y [HIn Heqb]].
        apply eqb_eq in Heqb as Heq.
        subst.
        rewrite In__mdrop...
      } {
        assert (closed vb). eapply RV_closed_1...
        assert (closed vb'). eapply RV_closed_2...
        apply RG_env_closed in HRG as Hclss...
        destruct Hclss as [Hcls__env Hcls__env'].
        rewrite <- subst_bnr__msubst_bnr' in Hev__e_f...
        replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
          (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev__e_f...
        
        unfold btvbs in Hev__e_f.
        simpl in Hev__e_f.
        rewrite <- msubstA_bnr__bvbs.
        rewrite <- msubstA_bnr__bvbs in Hev__e_f.

        apply Util.existsb_nexists in Hexb.
        rewrite not_In__mdrop.
        - replace (concat (map btvb bs)) with (btvbs bs) in Hev__e_f...
          rewrite <- subst_msubst'' in Hev__e_f...
          + eapply RG_env_closed_1.
            eapply RG_drop...
            eauto_LR.
          + intros Hcon.
            apply Hexb.
            exists x.
            rewrite eqb_refl.
            eauto.
        - intros Hcon.
          apply Hexb.
          exists x.
          rewrite eqb_refl.
          eauto.
      }
  - (* E_Error_Let_TermBind*)
    rename j1 into jb.
    rename H7 into Hev__Err.

    assert (HRC__tb :
      RC k Tbn rho
        (msubst_term env (msubstA_term (msyn1 rho) tb))
        (msubst_term env' (msubstA_term (msyn2 rho) tb'))  
      )...
    clear IH__tb.

    eapply RC_to_RV with (j := jb) (e_f := Error T') in HRC__tb as temp...
    destruct temp as [vb' [jb' [Hev__vb' HRV__vb]]].
    clear Hev__Err.
    clear HRC__tb.

    eapply RV_error in HRV__vb as temp...
    
    destruct temp as [ [Hnerr Hnerr'] | [Herr Herr']].
    + exfalso. eapply Hnerr. econstructor.
    + inversion Herr'. subst.

      eexists. eexists.
      split. {
        rewrite msubstA_LetNonRec.
        rewrite msubstA_BindingsNonRec_cons.
        rewrite msubstA_TermBind.
        rewrite msubst_LetNonRec.
        rewrite msubst_BindingsNonRec_cons.
        rewrite msubst_TermBind.

        eapply E_Let.
        eapply E_Error_Let_TermBind...
      }
      
      split. {
        inversion Htyp__ih. subst.
        simpl in H9.
        eapply msubstT_preserves_kinding_1 in H9 as H10...
        eapply strong_normalisation in H10 as H11...
        destruct H11.
        
        eexists. split...
      }

      split. {
        inversion Htyp__ih. subst.
        simpl in H9.
        eapply msubstT_preserves_kinding_2 in H9 as H10...
        eapply strong_normalisation in H10 as H11...
        destruct H11.
        
        eexists. split...
      }
      right...
Qed.
