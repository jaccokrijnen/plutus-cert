Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Require Import Arith.
Require Import Coq.Lists.List.

Lemma compatibility_LetNonRec_nil : forall Delta Gamma t t' T,
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec nil t) (Let NonRec nil t') T.
Proof with eauto_LR.
  intros Delta Gamma t t' T Hkind__T IHLR__t.
  unfold LR_logically_approximate.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split... 
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_LetNonRec_nil. rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil. rewrite msubst_LetNonRec_nil.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.
  inversion H3. subst.
  rename j0 into j_1.
  rename H3 into Hev'__e_f.
  rename H0 into Hev''__e_f.
  

  assert (HRC__t : RC k T rho 
    (msubst_term env (msubstA_term (msyn1 rho) t))
    (msubst_term env' (msubstA_term (msyn2 rho) t'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
  destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

  eexists. eexists.

  split. eapply E_Let. eapply E_Let_Nil...
  split. eapply RV_typable_empty_1...
  split. eapply RV_typable_empty_2...

  eapply RV_condition... 
  eapply RV_monotone...
Qed.

Lemma mupdate_flatten : forall {X : Type} (m : partial_map X) x l,
    mupdate m (flatten (x :: l)) = mupdate (mupdate m x) (flatten l).
Proof.
  intros.
  unfold flatten.
  simpl.
  rewrite concat_app.
  simpl.
  rewrite app_nil_r.
  rewrite <- mupdate_app.
  reflexivity.
Qed.


Lemma compatibility_LetNonRec_cons : forall Delta Gamma b bs t b' bs' t' T,
    forall Delta_ih Gamma_ih,
      Delta_ih = mupdate Delta (binds_Delta b) ->
      Gamma_ih = mupdate Gamma (binds_Gamma b) ->
      LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (Let NonRec bs' t') T ->
      LR_logically_approximate_binding Delta Gamma b b' ->
      LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') T.
Proof with eauto_LR.
  intros Delta Gamma b bs t b' bs' t' T Delta_ih Gamma_ih Heq__Delta_ih Heq__Gamma_ih IHLR__ih IHLR__b.
  subst.

  destruct IHLR__ih as [Htyp__ih [Htyp__ih' IH__ih]].
  destruct IHLR__b as [Htyp__b [Htyp__b' IH__b]].

  inversion Htyp__ih. subst.
  inversion Htyp__ih'. subst.

  assert (Heq__bindsD : binds_Delta b = binds_Delta b'). {
    destruct b, b'.
    all: try solve [destruct v; destruct v0; auto].
    all: try solve [destruct v; exfalso; auto].
    all: try solve [inversion IH__b; auto].
  }

  assert (Heq__bindsG : binds_Gamma b = binds_Gamma b'). {
    destruct b, b'.
    all: try solve [destruct v; destruct v0; destruct IH__b as [Heq1 [Heq2 [Heq3 _]]]; subst; auto].
    all: try solve [destruct v; exfalso; auto].
    all: try solve [inversion IH__b; auto].
  }

  rewrite Heq__bindsD in H6.
  rewrite Heq__bindsG in H6.
  rewrite Heq__bindsD in H9.
  rewrite Heq__bindsG in H9.

  clear Heq__bindsD Heq__bindsG.

  rewrite <- mupdate_flatten in H7.
  rewrite <- mupdate_flatten in H7.
  rewrite <- mupdate_flatten in H9.
  rewrite <- mupdate_flatten in H9.

  split...
  split...

  intros k rho env env' cG cD Heq__Delta Heq__Gamma HRD HRG.
  subst.

  autorewrite with RC.

  clear H5 H7 H6 H9.
  clear Htyp__ih Htyp__ih' Htyp__b Htyp__b'.

  destruct b, b'.
  - destruct v, v0.
    
    destruct IH__b as [Heq1 [Heq2 [Heq3 IHLR__tb]]].
    subst.

    rename s1 into x.
    rename t2 into Tb.
    rename t0 into tb.
    rename t1 into tb'.
  
    rewrite msubstA_LetNonRec. rewrite msubstA_LetNonRec.
    rewrite msubstA_BindingsNonRec_cons. rewrite msubstA_BindingsNonRec_cons.
    rewrite msubst_LetNonRec. rewrite msubst_LetNonRec.
    rewrite msubst_BindingsNonRec_cons. rewrite msubst_BindingsNonRec_cons.
    rewrite msubstA_TermBind. rewrite msubstA_TermBind.
    rewrite msubst_TermBind. rewrite msubst_TermBind.

    intros j Hlt__j e_f Hev__e_f.
    
    inversion Hev__e_f. subst.
    clear Hev__e_f. rename H3 into Hev__e_f.
    inversion Hev__e_f. subst.
    clear Hev__e_f.
    rename H7 into Hev__vb.
    rename H8 into Hev__e_f.

    destruct IHLR__tb as [_ [_ IH__tb]].
    assert (HRC__tb :
      RC k Tb rho
        (msubst_term env (msubstA_term (msyn1 rho) tb))
        (msubst_term env' (msubstA_term (msyn2 rho) tb'))  
    )...
    clear IH__tb.

    eapply RC_to_RV with (j := jb) (e_f := vb) in HRC__tb as temp...
    destruct temp as [vb' [jb' [Hev__vb' HRV__vb]]].
    clear Hev__vb.
    clear HRC__tb.

    assert (HRC__ih :
      RC (k - jb -1) T rho
        <{ /[ (x, vb) :: drop x env /] ( /[[ msyn1 rho /] {Let NonRec bs t} ) }>
        <{ /[ (x, vb') :: drop x env' /] ( /[[ msyn2 rho /] {Let NonRec bs' t'} ) }>
    ). {
      apply IH__ih with (ct := (x, Tb) :: drop x cG) (ck := cD).
      - reflexivity.
      - apply mupdate_drop.
      - assumption.
      - assert (closed vb). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_1...
        }
        assert (closed vb'). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_2...
        }
        replace vb with (msubstA_term (msyn1 rho) vb) by (eapply msubstA_closed; eauto).
        replace vb' with (msubstA_term (msyn2 rho) vb') by (eapply msubstA_closed; eauto).
        apply RG_cons.
        + apply RV_monotone with (k := k - jb) (ck := cD)...
          rewrite msubstA_closed...
          rewrite msubstA_closed...
        + apply RG_monotone with (k := k) (ck := cD)...
          apply RG_drop...
    }
    clear IH__ih.

    apply RC_to_RV with (j := j0) (e_f := e_f) in HRC__ih as temp...
    * destruct temp as [e'_f [j0' [Hev__e'_f HRV0]]].
      clear Hev__e_f.

      rewrite msubstA_LetNonRec in Hev__e'_f.
      rewrite msubst_LetNonRec in Hev__e'_f.

      rewrite <- msubstA_bnr__bvbs in Hev__e'_f.

      inversion Hev__e'_f. subst.

      eexists. eexists.
      split. {
        apply E_Let.
        apply E_ConsB_NonRec with (vb := vb') (jb := jb') (v := e'_f) (j := j0')...
        simpl.
        rewrite <- msubst_bnr__bound_vars.
        rewrite <- msubstA_bnr__bvbs.
        destruct (existsb (eqb x) (bvbs bs')) eqn:Hexb.
        - assert (closed vb). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_1...
          }
          assert (closed vb'). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_2...
          }
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
        - assert (closed vb). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_1...
          }
          assert (closed vb'). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_2...
          }
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

      split. eapply RV_typable_empty_1...
      split. eapply RV_typable_empty_2...

      eapply RV_condition...
      replace (k - (jb + 1 + j0)) with (k - jb - 1 - j0)...
    * rewrite msubstA_LetNonRec.
      rewrite msubst_LetNonRec. 
      apply E_Let.

      simpl.
      simpl in Hev__e_f.

      rewrite <- msubst_bnr__bound_vars in Hev__e_f.
      rewrite <- msubstA_bnr__bvbs in Hev__e_f.

      destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb. {
        assert (closed vb). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_1...
        }
        assert (closed vb'). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_2...
        }
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
        assert (closed vb). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_1...
        }
        assert (closed vb'). {
          eapply typable_empty__closed.
          eapply RV_typable_empty_2...
        }
        apply RG_env_closed in HRG as Hclss...
        destruct Hclss as [Hcls__env Hcls__env'].
        rewrite <- subst_bnr__msubst_bnr' in Hev__e_f...
        replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
          (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev__e_f...
        
        unfold btvbs in Hev__e_f.
        simpl in Hev__e_f.
        rewrite <- msubstA_bnr__bvbs.
        rewrite <- msubstA_bnr__bvbs in Hev__e_f.

        apply existsb_nexists in Hexb.
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
  - destruct v. exfalso. auto.
  - destruct v. exfalso. auto.
  - exfalso. auto.
  - 
Admitted.