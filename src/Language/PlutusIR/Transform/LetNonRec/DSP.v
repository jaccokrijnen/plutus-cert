Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.




(** * [CNR] is semantics preserving *)

(** ** Translation relation specific compatibility lemmas *)

Lemma compatibility_LetNonRec_nil__desugar : forall Delta Gamma t t' T,
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec nil t) t' T.
Proof with eauto_LR.
  intros Delta Gamma t t' Tn Hkind__T IHLR__t.
  unfold LR_logically_approximate.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  inversion H3. subst.
  rename j0 into j_1.
  rename H3 into Hev'__e_f.
  rename H0 into Hev''__e_f.
  

  assert (HRC__t : RC k Tn rho 
    (msubst_term env (msubstA_term (msyn1 rho) t))
    (msubst_term env' (msubstA_term (msyn2 rho) t'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
  destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

  eexists. eexists.

  split...

  split... eapply RV_typable_empty_1...
  split... eapply RV_typable_empty_2...

  eapply RV_condition... 
  eapply RV_monotone...
Qed.

Lemma compatibility_TermBind__desugar : forall Delta Gamma t t' Tn b bs fbs' tb tb' x Tb Tbn,
  Delta |-* Tb : Kind_Base ->
  normalise Tb Tbn ->
  forall Delta_ih Gamma_ih bsGn,
    b = TermBind Strict (VarDecl x Tb) tb ->
    Delta_ih = mupdate Delta (binds_Delta b) ->
    map_normalise (binds_Gamma b) bsGn ->
    Gamma_ih = mupdate Gamma bsGn ->
    LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (fold_right apply t' fbs') Tn ->
    LR_logically_approximate Delta Gamma tb tb' Tbn ->
    LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Apply (LamAbs x Tb (fold_right apply t' fbs')) tb') Tn.
Proof with eauto_LR. 
  intros Delta Gamma t t' Tn b bs fbs' tb tb' x Tb Tbn.
  intros Hkind__Tb Hnorm__Tbn.
  intros Delta_ih Gamma_ih bsGn.
  intros Heq__b Heq__Delta_ih Hmapnorm__bsGn Heq__Gamma_ih IHLR__ih IHLR__tb.
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
    - rewrite mupdate_app...
  }

  split. {
    eapply T_Apply...
    eapply T_LamAbs...
    simpl in Hmapnorm__bsGn.
    inversion Hmapnorm__bsGn. subst.
    inversion H3. subst.
    eapply normalisation__deterministic in Hnorm__Tbn...
    subst...
  }
 
  intros k rho env env' ct ck Heq__Delta Heq__Gamma HRD HRG.
  subst.

  rewrite msubstA_LetNonRec.
  rewrite msubstA_BindingsNonRec_cons.
  rewrite msubstA_TermBind.
  rewrite msubst_LetNonRec.
  rewrite msubst_BindingsNonRec_cons.
  rewrite msubst_TermBind.

  rewrite msubstA_Apply.
  rewrite msubstA_LamAbs.
  rewrite msubst_Apply.
  rewrite msubst_LamAbs.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  clear Hev__e_f. rename H3 into Hev__e_f.
  inversion Hev__e_f; subst.
  - clear Hev__e_f.
    rename v1 into vb.
    rename j1 into jb.
    rename H7 into Hev__vb.
    rename H8 into Hnerr__vb.
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
        <{ /[ (x, vb') :: drop x env' /] ( /[[ msyn2 rho /] {fold_right apply t' fbs'} ) }>
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
        + apply RG_monotone with (k := k) (ck := ck)...
          apply RG_drop...
    }
    clear IH__ih.

    apply RC_to_RV with (j := j2) (e_f := e_f) in HRC__ih as temp...
    * destruct temp as [e'_f [j2' [Hev__e'_f HRV0]]].
      clear Hev__e_f.

      eexists. eexists.
      split. {
        eapply E_Apply...
        - eapply E_LamAbs.
        - eapply RV_error in HRV__vb as temp...
          destruct temp as [ [Herr Herr'] | [Hnerr Hnerr']]...
        - rewrite <- subst_msubst'...
          + eapply RV_closed_2...
          + eapply RG_env_closed_2...
      }

      split... eapply RV_typable_empty_1...
      split... eapply RV_typable_empty_2...
    
      eapply RV_condition...
      eapply RV_monotone...
    * rewrite msubstA_LetNonRec.
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
  - admit.
Admitted.

(** ** Predicates *)

Definition P_has_type Delta Gamma t T : Prop := 
  forall t',
    CNR_Term t t' ->
    LR_logically_approximate Delta Gamma t t' T.

Definition P_constructor_well_formed Delta c Tr : Prop := Delta |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop := 
  (
    forall bs',
      Congruence.Cong_Bindings CNR_Term bs bs' ->
      forall Delta_t Gamma_t bsGn t t' T,
        Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Gamma_t = mupdate Gamma bsGn  ->
        LR_logically_approximate Delta_t Gamma_t t t' T ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T
  ) /\ (
    forall fbs',
      CNR_Bindings bs fbs' ->
      forall Delta_t Gamma_t bsGn t t' T,
        Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Gamma_t = mupdate Gamma bsGn  ->
        LR_logically_approximate Delta_t Gamma_t t t' T ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (fold_right apply t' fbs') T
  ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b : Prop := 
  (
    forall b',
      Congruence.Cong_Binding CNR_Term b b' ->
      forall Delta_t Gamma_t bsGn t t' T bs bs',
        Delta_t = mupdate Delta (binds_Delta b) ->
        map_normalise (binds_Gamma b) bsGn ->
        Gamma_t = mupdate Gamma bsGn ->
        LR_logically_approximate Delta_t Gamma_t (Let NonRec bs t) (Let NonRec bs' t') T ->
        LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') T
  ) /\ (
    forall fb',
      CNR_Binding b fb' ->
      forall Delta_t Gamma_t bsGn t t' T bs fbs',
        Delta_t = mupdate Delta (binds_Delta b) ->
        map_normalise (binds_Gamma b) bsGn ->
        Gamma_t = mupdate Gamma bsGn ->
        LR_logically_approximate Delta_t Gamma_t (Let NonRec bs t) (fold_right apply t' fbs') T ->
        LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (fold_right apply t' (fb' :: fbs')) T
  ).

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

(** ** The main theorem *)

Theorem CNR_Term__DSP : forall Delta Gamma e T,
    Delta ,, Gamma |-+ e : T ->
    P_has_type Delta Gamma e T.
Proof with eauto_LR.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : intros; autounfold; intros; subst.
  all : try solve [
    inversion X; subst;
    inversion X0; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    inversion X0; subst;
    inversion X1; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    eauto with typing
  ].
  - (* T_Let *)
    inversion X; subst.
    + eapply H3...
    + inversion X0; subst.
      eapply H3...

  - (* W_NilB_NonRec *)
    split. all: intros. all: subst.
    + inversion X. subst.
      inversion H0... subst.
      simpl in H2.
      eapply compatibility_LetNonRec_nil...
      admit.
    + inversion X. subst.
      inversion H0. subst.
      simpl in H2.
      eapply compatibility_LetNonRec_nil__desugar...
      admit.
  - (* W_ConsB_NonRec *)
    split. all: intros. all: subst.
    + inversion X. subst.
      inversion X0; subst.
      * destruct v. 

        simpl in H5.
        unfold flatten in H5.
        simpl in H5.
        rewrite concat_app in H5.
        simpl in H5.
        apply map_normalise__app in H5 as H6.
        destruct H6 as [l1n [l2n [Hn__l1n [Hn__l2n Heql]]]].
        simpl in Hn__l2n.
        inversion Hn__l2n. subst.
        inversion H10. subst.

        simpl in H1.
        inversion H1. subst.
        inversion H12. subst.
        
        eapply normalisation__deterministic in H11... 
        subst.

        eapply H0...
        eapply H3...

        simpl in H7.
        rewrite mupdate_app in H7.
        unfold flatten in H7.
        simpl in H7.
        rewrite concat_app in H7.
        simpl in H7.
        rewrite app_nil_r in H7.

        eapply H7.
      * admit.
      * admit.
    + inversion X. subst.
      inversion X0. subst.
      
      simpl in H5.
      unfold flatten in H5.
      simpl in H5.
      rewrite concat_app in H5.
      simpl in H5.
      apply map_normalise__app in H5 as H6.
      destruct H6 as [l1n [l2n [Hn__l1n [Hn__l2n Heql]]]].
      simpl in Hn__l2n.
      inversion Hn__l2n. subst.
      inversion H10. subst.

      simpl in H1.
      inversion H1. subst.
      inversion H12. subst.
      
      eapply normalisation__deterministic in H11... 
      subst.

      eapply H0...
      eapply H3...
      
      simpl in H7.
      rewrite mupdate_app in H7.
      unfold flatten in H7.
      simpl in H7.
      rewrite concat_app in H7.
      simpl in H7.
      rewrite app_nil_r in H7.

      eapply H7.

  - (* W_Term *)
    split. all: intros. all: subst.
    + inversion X. subst.
      eauto with DSP_compatibility_lemmas.
    + inversion X. subst.
      eapply compatibility_TermBind__desugar...
  - (* W_Type *)
    split. 
    + intros. subst.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas.
    + intros. subst.
      inversion X0.
  - (* W_Data *)
    split.
    + intros. subst.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas typing.
    + intros. subst.
      inversion X0.
Admitted.