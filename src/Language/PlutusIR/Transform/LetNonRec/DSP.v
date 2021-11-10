Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.




(** * [CNR] is semantics preserving *)

(** ** Translation relation specific compatibility lemmas *)

Lemma compatibility_LetNonRec_nil__desugar : forall Delta Gamma t t' T,
    LR_logically_approximate Delta Gamma t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec nil t) t' T.
Proof with eauto_LR.
  intros Delta Gamma t t' T IHLR__t.
  unfold LR_logically_approximate.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil.

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

  split...

  split... eapply RV_typable_empty_1...
  split... eapply RV_typable_empty_2...

  eapply RV_condition... 
  eapply RV_monotone...
Qed.

Lemma compatibility_TermBind__desugar : forall Delta Gamma t t' T b bs fbs' tb tb' x Tb,
  Delta |-* Tb : Kind_Base ->
  forall Delta_ih Gamma_ih,
    b = TermBind Strict (VarDecl x Tb) tb ->
    Delta_ih = mupdate Delta (binds_Delta b) ->
    Gamma_ih = mupdate Gamma (binds_Gamma b) ->
    LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (fold_right apply t' fbs') T ->
    LR_logically_approximate Delta Gamma tb tb' Tb ->
    LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Apply (LamAbs x Tb (fold_right apply t' fbs')) tb') T.
Proof with eauto_LR. 
  intros Delta Gamma t t' T b bs fbs' tb tb' x Tb Hkind__Tb Delta_ih Gamma_ih Heq__b Heq__Delta_ih Heq__Gamma_ih IHLR__ih IHLR__tb.
  subst.

  destruct IHLR__ih as [Htyp__ih [Htyp__ih' IH__ih]].
  destruct IHLR__tb as [Htyp__tb [Htyp__tb' IH__tb]].

  inversion Htyp__ih. subst.

  rewrite <- mupdate_flatten in H7.
  rewrite <- mupdate_flatten in H7.

  split... 
  split...

  intros k rho env env' cG cD Heq__Delta Heq__Gamma HRD HRG.
  subst.

  autorewrite with RC.

  clear H5 H7.
  clear Hkind__Tb.
  clear Htyp__ih Htyp__ih' Htyp__tb Htyp__tb'.

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

  intros j Hlt__j e_f Hev__e_f.
  
  inversion Hev__e_f. subst.
  clear Hev__e_f. rename H3 into Hev__e_f.
  inversion Hev__e_f. subst.
  clear Hev__e_f.
  rename H7 into Hev__vb.
  rename H8 into Hev__e_f.

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
    RC (k - jb - 1) T rho
      <{ /[ (x, vb) :: drop x env /] ( /[[ msyn1 rho /] {Let NonRec bs t} ) }>
      <{ /[ (x, vb') :: drop x env' /] ( /[[ msyn2 rho /] {fold_right apply t' fbs'} ) }>
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

    eexists. eexists.
    split. {
      eapply E_Apply...
      - eapply E_LamAbs.
      - rewrite <- subst_msubst'...
        + eapply typable_empty__closed...
          eapply RV_typable_empty_2...
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
Qed.

(** ** Predicates *)

Definition P_has_type Delta Gamma e T := 
  forall e',
    CNR_Term e e' ->
    LR_logically_approximate Delta Gamma e e' T.

Definition P_constructor_well_formed Delta c := Delta |-ok_c c.

Definition P_bindings_well_formed_nonrec Delta Gamma bs := 
  (
    forall bs',
      Congruence.Cong_Bindings CNR_Term bs bs' ->
      forall Delta_t Gamma_t t t' T,
        Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
        Gamma_t = mupdate Gamma (flatten (List.map binds_Gamma bs)) ->
        LR_logically_approximate Delta_t Gamma_t t t' T ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T
  ) /\ (
    forall fbs',
      CNR_Bindings bs fbs' ->
      forall Delta_t Gamma_t t t' T,
        Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
        Gamma_t = mupdate Gamma (flatten (List.map binds_Gamma bs)) ->
        LR_logically_approximate Delta_t Gamma_t t t' T ->
        LR_logically_approximate Delta Gamma (Let NonRec bs t) (fold_right apply t' fbs') T
  ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b := 
  (
    forall b',
      Congruence.Cong_Binding CNR_Term b b' ->
      LR_logically_approximate_binding Delta Gamma b b'
  ) /\ (
    forall fb',
      CNR_Binding b fb' ->
      forall Delta_t Gamma_t t t' T bs fbs',
        Delta_t = mupdate Delta (binds_Delta b) ->
        Gamma_t = mupdate Gamma (binds_Gamma b) ->
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

  all : autounfold; intros; subst.
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
    inversion X.
    + subst.
      eapply H2...
    + subst.
      inversion X0. subst.
      eapply H2...
  - (* T_NilB_NonRec *)
    split.
    + intros. subst.
      inversion X. subst.
      eauto with DSP_compatibility_lemmas.
    + intros. subst.
      inversion X. subst.
      simpl.
      apply compatibility_LetNonRec_nil__desugar...
  - (* T_ConsB_NonRec *)
    destruct H0.
    destruct H2.
    split.
    + intros. subst.
      inversion X. subst.
      eauto with DSP_compatibility_lemmas typing.
    + intros. subst.
      inversion X. subst.
      inversion X0. subst.

      clear H2.
      clear H0.

      eapply H3...
      eapply H4...
      simpl in H7.
      rewrite mupdate_flatten in H7.
      rewrite mupdate_flatten in H7.
      apply H7.
  - (* W_Term *)
    split.
    + intros. subst.
      inversion X. subst.
      eauto with DSP_compatibility_lemmas.
    + intros. subst.
      inversion X. subst.
      simpl.
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
Qed.