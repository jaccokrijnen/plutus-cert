Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Util.

Require Import Arith.
Require Import Coq.Lists.List.

Lemma In__mdrop : forall {X} ns ss x s,
    List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = @mdrop X ns ss.
Proof.
  induction ns; intros.
  - destruct H.
  - simpl.
    destruct (x =? a) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      * symmetry in H. 
        apply Hneq in H.
        destruct H.
      * eapply IHns.
        assumption. 
Qed.

Lemma not_In__mdrop : forall {X} ns ss x s,
    ~ List.In x ns ->
    @mdrop X ns ((x, s) :: ss) = (x, s) :: @mdrop X ns ss.
Proof.
  induction ns; intros.
  - reflexivity.
  - simpl.
    destruct (x =? a) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      eapply IHns.
      intros Hcon.
      apply H.
      right.
      assumption.
Qed.

Lemma subst_b__bound_vars : forall x s b,
    bvb b = bvb <{ [s/x][b] b }>.
Proof. intros. induction b. all: eauto. destruct v. eauto. Qed.

Lemma subst_bnr__bound_vars : forall x s bs,
    bvbs bs = bvbs <{ [s/x][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb x) (bvb a)) eqn:Hexb.
    + unfold bvbs.
      simpl.
      f_equal.
      apply subst_b__bound_vars.
    + unfold bvbs.
      simpl.
      f_equal.
      * apply subst_b__bound_vars.
      * assumption.
Qed.

Lemma msubst_bnr__bound_vars : forall bs ss,
    bvbs bs = bvbs <{ /[ ss /][bnr] bs }>.
Proof. Admitted.

Lemma substA_b__bound_tyvars : forall a T b,
    btvb b = btvb <{ [[T/a][b] b }>.
Proof. intros. induction b. all: eauto. destruct v; eauto. destruct d; eauto. Qed.

Lemma substA_bnr__bound_tyvars : forall a T bs,
    btvbs bs = btvbs <{ [[T/a][bnr] bs }>.
Proof. 
  intros. 
  induction bs.
  - reflexivity.
  - simpl.
    destruct (List.existsb (eqb a) (btvb a0)) eqn:Hfind.
    + unfold btvbs.
      simpl.
      f_equal.
      apply substA_b__bound_tyvars.
    + unfold btvbs.
      simpl.
      f_equal.
      * apply substA_b__bound_tyvars.
      * assumption.
Qed.

Lemma msubstA_bnr__bvbs : forall bs ss,
    bvbs bs = bvbs <{ /[[ ss /][bnr] bs }>.
Proof. Admitted.
    
Lemma msubst_LetNonRec_nil : forall ss e,
    msubst_term ss (Let NonRec nil e) = Let NonRec nil (msubst_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_LetNonRec : forall ss bs e,
    msubst_term ss (Let NonRec bs e) = Let NonRec (msubst_bindings_nonrec ss bs) (msubst_term (mdrop (bvbs bs) ss) e).
Proof with auto.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. simpl.
    destruct (existsb (eqb s) (bvbs bs)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop...
      erewrite subst_bnr__bound_vars.
      eapply IHss.
    + rewrite not_In__mdrop...
      * simpl.
        erewrite subst_bnr__bound_vars.
        eapply IHss.
      * intros Hcon.
        eapply existsb_nexists.
        -- eapply Hexb.
        -- exists s.
           rewrite eqb_refl.
           auto.
Qed.

Lemma msubst_TermBind : forall ss stricty x T e,
    msubst_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x T) (msubst_term ss e). 
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubst_BindingsNonRec_cons : forall ss b bs,
    msubst_bindings_nonrec ss (b :: bs) = msubst_binding ss b :: msubst_bindings_nonrec (mdrop (bvb b) ss) bs.
Proof.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. 
    simpl.
    destruct (existsb (eqb s) (bvb b)) eqn:Hexb.
    + apply existsb_exists in Hexb.
      destruct Hexb as [x [HIn Heqb]].
      apply eqb_eq in Heqb as Heq.
      subst.
      rewrite In__mdrop.
      * erewrite subst_b__bound_vars.  
        eapply IHss.
      * assumption.
    + apply existsb_nexists in Hexb.
      rewrite not_In__mdrop.
      * simpl.
        erewrite subst_b__bound_vars.
        eapply IHss.
      * intros Hcon.
        apply Hexb.
        exists s.
        rewrite eqb_refl.
        auto.
Qed.

Lemma msubstA_LetNonRec_nil : forall ss e,
    msubstA_term ss (Let NonRec nil e) = Let NonRec nil (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_LetNonRec : forall ss bs e,
    msubstA_term ss (Let NonRec bs e) = Let NonRec (msubstA_bindings_nonrec ss bs) (msubstA_term (mdrop (btvbs bs) ss) e).
Proof. Admitted.

Lemma msubstA_TermBind : forall ss stricty x T e,
    msubstA_binding ss (TermBind stricty (VarDecl x T) e) = TermBind stricty (VarDecl x (msubstT ss T)) (msubstA_term ss e).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_BindingsNonRec_cons : forall ss b bs,
    msubstA_bindings_nonrec ss (b :: bs) = msubstA_binding ss b :: msubstA_bindings_nonrec (mdrop (btvb b) ss) bs.
Proof.
  induction ss; intros.
  - rewrite mdrop_nil. reflexivity.
  - destruct a. 
    simpl.
    destruct (List.find (eqb s) (btvb b)) eqn:Hfind.
    + simpl. 
Admitted.

Inductive LR_logically_approximate_bindings_nonrec : Delta -> Gamma -> list Binding -> list Binding -> Prop :=
  | LR_NonRec_Nil : forall Delta Gamma,
      LR_logically_approximate_bindings_nonrec Delta Gamma nil nil
  | LR_NonRec_Cons : forall Delta Gamma b b' Delta' Gamma' bs bs',
      LR_logically_approximate_binding Delta Gamma b b' ->
      (Delta', Gamma') = Implementations.append (binds b) (Delta, Gamma) ->
      binds b = binds b' ->
      LR_logically_approximate_bindings_nonrec Delta' Gamma' bs bs' ->
      LR_logically_approximate_bindings_nonrec Delta Gamma (b :: bs) (b' :: bs').

Lemma LR_la_bnr__oks : forall Delta Gamma bs bs',
    LR_logically_approximate_bindings_nonrec Delta Gamma bs bs' ->
    (Delta, Gamma) |-oks_nr bs /\ (Delta, Gamma) |-oks_nr bs' /\ List.map binds bs = List.map binds bs'.
Proof.
  intros.
  induction H.
  - eauto with typing.
  - split.
    + econstructor.
      * apply H.
      * rewrite <- H0.
        apply IHLR_logically_approximate_bindings_nonrec.
    + split. 
      * econstructor.
        -- apply H.
        -- rewrite <- H1.
          rewrite <- H0.
          apply IHLR_logically_approximate_bindings_nonrec.
      * simpl.
        rewrite H1.
        f_equal.
        apply IHLR_logically_approximate_bindings_nonrec.
Qed.

Lemma msubst_term__fold : forall ss x v t,
    msubst_term ss <{ [v / x] t }> = msubst_term ((x, v) :: ss) t.
Proof. induction ss; intros; auto. Qed.

Lemma msubst_bindings_nonrec__fold : forall ss x v bs,
    msubst_bindings_nonrec ss <{ [v / x][bnr] bs }> = msubst_bindings_nonrec ((x, v) :: ss) bs.
Proof. induction ss; intros; auto. Qed.

Lemma compatibility_LetNonRec : forall bs Delta Gamma t bs' t' T,
    forall Delta' Gamma',
      (Delta', Gamma') = append (flatten (List.map binds bs)) (Delta, Gamma) ->
      LR_logically_approximate Delta' Gamma' t t' T ->
      LR_logically_approximate_bindings_nonrec Delta Gamma bs bs' ->
      LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T.
Proof with eauto_LR.
  induction bs.
  - intros Delta Gamma t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bs.
    unfold LR_logically_approximate.

    destruct IH_LR__t as [Htyp__t [Htyp__t' IH__t]].
    inversion IH_LR__bs. subst.

    split...
    split...

    intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
    subst.

    autorewrite with RC.

    split...
    split...

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
    ). {
      simpl in Hbinds. 
      rewrite flatten_nil in Hbinds.
      rewrite append_emptyContext_l in Hbinds.
      inversion Hbinds. subst.
      eapply IH__t...
    }

    apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

    eexists. eexists.

    split. eapply E_Let. eapply E_NilB_NonRec...

    eapply RV_condition... 
    eapply RV_monotone...

  - intros Delta Gamma t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bbs.
    unfold LR_logically_approximate.
    rename a into b.

    inversion IH_LR__bbs. subst.

    rename bs'0 into bs'.
    rename Delta'0 into Delta''.
    rename Gamma'0 into Gamma''.
    rename H1 into IH_LR__b.
    rename H2 into Hbinds''.
    rename H7 into IH_LR__bs.

    assert (IH_LR__let : 
      LR_logically_approximate Delta'' Gamma''
        (Let NonRec bs t) (Let NonRec bs' t') T
    ). {
      eapply IHbs...
      simpl in Hbinds.
      unfold flatten in Hbinds.
      simpl in Hbinds.
      rewrite concat_append in Hbinds.
      simpl in Hbinds.
      rewrite append_emptyContext_r in Hbinds.
      apply skip. (* TODO *)
    }

    destruct IH_LR__t as [Htyp__t [Htyp__t' IH__t]].
    destruct IH_LR__b as [Htyp__b [Htyp__b' IH__b]].
    eapply LR_la_bnr__oks in IH_LR__bbs.
    destruct IH_LR__bbs as [Htyp__bbs [Htyp__bbs' Heqbinds__bbs]].

    remember Hbinds as Hbinds'. clear HeqHbinds'.
    rewrite Heqbinds__bbs in Hbinds'.

    split...
    split...

    intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
    subst.

    autorewrite with RC.

    split...
    split...

    (* Some context management *)
    clear IHbs.
    clear Htyp__t.
    clear Htyp__t'.
    clear Htyp__bbs.
    clear Htyp__bbs'.
    clear Heqbinds__bbs.
    clear Htyp__b.
    clear Htyp__b'.
    clear H5.
    clear IH_LR__bs. 
    clear IH__t.

    destruct b, b'.
    + destruct v. destruct v0.
      rename s into s.
      rename s0 into s'.
      rename s1 into x.
      rename s2 into x'.
      rename t2 into Tb.
      rename t3 into Tb'.
      rename t0 into tb.
      rename t1 into tb'.

      destruct IH__b as [Heq1 [Heq2 [Heq3 IH_LR__tb]]].
      subst.

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
      rename H7 into Hev__vb.
      rename H8 into Hev'__e_f.

      destruct IH_LR__tb as [_ [_ IH__tb]].
      assert (HRC__tb :
        RC k Tb rho
          (msubst_term env (msubstA_term (msyn1 rho) tb))
          (msubst_term env' (msubstA_term (msyn2 rho) tb'))  
      )...

      eapply RC_to_RV with (j := jb) (e_f := vb) in HRC__tb as temp...
      destruct temp as [vb' [jb' [Hev__vb' HRV__vb]]].
      clear Hev__vb.

      destruct IH_LR__let as [_ [_ IH__let]].

      assert (HRC__let :
        RC (k - jb -1) T rho
          <{ /[ (x, vb) :: drop x env /] ( /[[ msyn1 rho /] {Let NonRec bs t} ) }>
          <{ /[ (x, vb') :: drop x env' /] ( /[[ msyn2 rho /] {Let NonRec bs' t'} ) }>
      ). {
        apply IH__let with (ct := (x, Tb) :: drop x ct) (ck := ck).
        - simpl in Hbinds''.
          rewrite append_singleton_l in Hbinds''.
          inversion Hbinds''. subst.
          reflexivity.
        - simpl in Hbinds''.
          rewrite append_singleton_l in Hbinds''.
          inversion Hbinds''. subst.
          simpl.
          apply mupdate_drop.
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
          + apply RV_monotone with (k := k - jb)...
            rewrite msubstA_closed...
            rewrite msubstA_closed...
          + apply RG_monotone with (k := k)...
            apply RG_drop...
      }

      apply RC_to_RV with (j := j0) (e_f := e_f) in HRC__let as temp...
      * destruct temp as [e'_f [j0' [Hev__e'_f HRV0]]].

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
            apply RG_env_closed in H_RG as Hclss.
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
            apply RG_env_closed in H_RG as Hclss.
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

        eapply RV_condition...
        replace (k - (jb + 1 + j0)) with (k - jb - 1 - j0)...
      * rewrite msubstA_LetNonRec.
        rewrite msubst_LetNonRec. 
        apply E_Let.

        simpl.
        simpl in Hev'__e_f.

        rewrite <- msubst_bnr__bound_vars in Hev'__e_f.
        rewrite <- msubstA_bnr__bvbs in Hev'__e_f.

        destruct (existsb (eqb x) (bvbs bs)) eqn:Hexb. {
          assert (closed vb). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_1...
          }
          assert (closed vb'). {
            eapply typable_empty__closed.
            eapply RV_typable_empty_2...
          }
          apply RG_env_closed in H_RG as Hclss.
          destruct Hclss as [Hcls__env Hcls__env'].
          rewrite <- subst_bnr__msubst_bnr' in Hev'__e_f...
          replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
            (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev'__e_f...
          
          unfold btvbs in Hev'__e_f.
          simpl in Hev'__e_f.
          rewrite <- msubstA_bnr__bvbs.
          rewrite <- msubstA_bnr__bvbs in Hev'__e_f.

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
          apply RG_env_closed in H_RG as Hclss.
          destruct Hclss as [Hcls__env Hcls__env'].
          rewrite <- subst_bnr__msubst_bnr' in Hev'__e_f...
          replace (concat (map bvb <{ /[[ msyn1 rho /][bnr] bs }>)) with
            (bvbs <{ /[[ msyn1 rho /][bnr] bs }>) in Hev'__e_f...
          
          unfold btvbs in Hev'__e_f.
          simpl in Hev'__e_f.
          rewrite <- msubstA_bnr__bvbs.
          rewrite <- msubstA_bnr__bvbs in Hev'__e_f.

          apply existsb_nexists in Hexb.
          rewrite not_In__mdrop.
          - replace (concat (map btvb bs)) with (btvbs bs) in Hev'__e_f...
            rewrite <- subst_msubst'' in Hev'__e_f...
            + eapply RG_env_closed_1.
              eapply RG_drop...
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
  + destruct v. exfalso. auto.
  + destruct v. exfalso. auto.
  + exfalso. auto.
  + 
Admitted.