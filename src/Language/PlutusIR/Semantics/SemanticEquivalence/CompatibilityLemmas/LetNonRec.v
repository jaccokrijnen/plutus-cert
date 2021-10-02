Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.

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

Lemma substb__bound_vars : forall x s b b',
    substitute_binding x s b b' ->
    bound_vars_in_binding b = bound_vars_in_binding b'.
Proof. intros. induction H. all: eauto. Qed.


Lemma substAb__bound_tyvars : forall x s b b',
    substituteA_binding x s b b' ->
    bound_tyvars_in_binding b = bound_tyvars_in_binding b'.
Proof. intros. induction H. all: eauto. Qed.

Lemma substA_bs_nr__bound_tyvars : forall x s bs bs',
    substituteA_bindings_nonrec x s bs bs' ->
    tyvars_bound_by_bindings bs = tyvars_bound_by_bindings bs'.
Proof.
  intros.
  induction H.
  - reflexivity.
  - destruct b. 
    all: inversion H0; subst.
    all: auto.
  - destruct b.
    all: inversion H0. subst.
    all: unfold tyvars_bound_by_bindings.
    all: simpl.
    all: try solve [f_equal; auto].
    apply IHsubstituteA_bindings_nonrec.
Qed.
    
Lemma msubst_LetNonRec_nil : forall ss e t',
    msubst_term ss (Let NonRec nil e) t' ->
    exists e',
      msubst_term ss e e' /\
      t' = Let NonRec nil e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists e.
    eauto using msubst_term__nil.
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2. subst.
    rename t'0 into e''.
    apply IHss in H5.
    destruct H5 as [e' [Hms__e' Heq]].
    subst.
    eauto using msubst_term__cons.
Qed.

Lemma msubst_LetNonRec_cons : forall ss b bs e t',
    msubst_term ss (Let NonRec (b :: bs) e) t' ->
    exists b' bs' e',
      msubst_binding ss b b' /\
      msubst_term (mdrop (bound_vars_in_binding b) ss) (Let NonRec bs e) (Let NonRec bs' e') /\
      t' = Let NonRec (b' :: bs') e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists b, bs, e.
    rewrite mdrop_nil.
    eauto using msubst_term__nil, msubst_binding__nil.
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    + subst.
      eapply IHss in H5 as H8.
      destruct H8 as [b'' [bs'' [e'' [Hms__b'' [Hms__t'' Heq]]]]].
      subst.
      exists b''.
      exists bs''.
      exists e''.
      split. {
        eapply msubst_binding__cons.
        all: eassumption.
      }
      split. {
        rewrite In__mdrop.
        - erewrite substb__bound_vars.
          all: eassumption.
        - eassumption.
      }
      reflexivity.
    + subst.
      eapply IHss in H5 as H9.
      destruct H9 as [b'' [bs'' [e'' [Hms__b'' [Hms__t'' Heq]]]]].
      subst.
      exists b''.
      exists bs''.
      exists e''.
      split. {
        eapply msubst_binding__cons.
        all: eassumption.
      }
      split. {
        rewrite not_In__mdrop.
        - erewrite substb__bound_vars.
          + eapply msubst_term__cons.
            all: eassumption.
          + eassumption.
        - eassumption.
      }
      reflexivity.
Qed.

Lemma msubst_TermBind : forall ss stricty x T e b',
    msubst_binding ss (TermBind stricty (VarDecl x T) e) b' ->
    exists e',
      msubst_term ss e e' /\
      b' = TermBind stricty (VarDecl x T) e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    eauto using msubst_term__nil.
  - inversion H. subst.
    inversion H2. subst.
    eapply IHss in H5.
    destruct H5 as [e'' [Hms__e'' Heq]].
    eauto using msubst_term__cons.
Qed.

Lemma msubstA_LetNonRec_nil : forall ss e t',
    msubstA ss (Let NonRec nil e) t' ->
    exists e',
      msubstA ss e e' /\
      t' = Let NonRec nil e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists e.
    eauto using msubstA_nil.
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    + subst.
      destruct H6.
    + subst.
      inversion H7. subst.
      rename t0' into e''.
      apply IHss in H5.
      destruct H5 as [e' [Hmsa__e' Heq]].
      subst.
      eauto using msubstA_cons.
Qed.

Lemma msubstA_LetNonRec_cons : forall ss b bs e t',
    msubstA ss (Let NonRec (b :: bs) e) t' ->
    exists b' bs' e',
      msubstA_binding ss b b' /\
      msubstA (mdrop (bound_tyvars_in_binding b) ss) (Let NonRec bs e) (Let NonRec bs' e') /\
      t' = Let NonRec (b' :: bs') e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists b, bs, e.
    rewrite mdrop_nil.
    eauto using msubstA_nil, msubstA_binding__nil.
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    + subst.
      inversion H8.
      * subst.
        eapply IHss in H5 as H9.
        destruct H9 as [b'' [bs'' [e'' [Hmsa__b'' [Hmsa__t'' Heq]]]]].
        subst.
        exists b''.
        exists bs''.
        exists e''.
        split. {
          eapply msubstA_binding__cons.
          all: eassumption.
        }
        split. {
          rewrite In__mdrop.
          - erewrite substAb__bound_tyvars.
            all: eassumption.
          - eassumption.
        }
        reflexivity.
      * subst.
        unfold bound_tyvars_in_bindings in H6.
        simpl in H6.
        apply List.in_app_or in H6.
        destruct H6.
        -- exfalso. auto.
        -- eapply IHss in H5 as H12.
           destruct H12 as [b'' [bs'' [e'' [Hmsa__b'' [Hmsa__t'' Heq]]]]].
           subst.
           exists b''.
           exists bs''.
           exists e''.
           split. {
             eapply msubstA_binding__cons.
             all: eassumption.
           }
           split. {
             rewrite not_In__mdrop.
             - eapply msubstA_cons.
               + eapply SA_Let1; eauto.
               + erewrite substAb__bound_tyvars.
                all: eassumption.
             - eassumption.
           }
          reflexivity.
    + subst.
      inversion H7.
      * subst.
        exfalso.
        apply H3.
        unfold bound_tyvars_in_bindings.
        simpl.
        apply List.in_or_app.
        left.
        assumption.
      * subst.
        eapply IHss in H5 as H13.
        destruct H13 as [b'' [bs'' [e'' [Hms__b'' [Hms__t'' Heq]]]]].
        subst.
        exists b''.
        exists bs''.
        exists e''.
        split. {
          eapply msubstA_binding__cons.
          all: eassumption.
        }
        split. {
          rewrite not_In__mdrop.
          - eapply msubstA_cons.
            + eapply SA_Let2; eauto.
              intros Hcon.
              apply H3.
              unfold bound_tyvars_in_bindings.
              simpl.
              apply List.in_or_app.
              right.
              assumption.
            + erewrite substAb__bound_tyvars.
            all: eassumption.
          - eassumption.
        }
        reflexivity.
Qed.

Lemma msubstA_TermBind : forall ss stricty x T e b',
    msubstA_binding ss (TermBind stricty (VarDecl x T) e) b' ->
    exists e',
      msubstA ss e e' /\
      b' = TermBind stricty (VarDecl x (msubstT ss T)) e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    eauto using msubstA_nil.
  - inversion H. subst.
    inversion H2. subst.
    eapply IHss in H5.
    destruct H5 as [e'' [Hmsa__e'' Heq]].
    eauto using msubstA_cons.
Qed.

Lemma inspect_eval__LetNonRec_nil : forall e j e_f,
    Let NonRec nil e =[j]=> e_f ->
    exists j_1, e =[j_1]=> e_f /\ j = j_1 + 1.
Proof.
  intros.
  inversion H. subst.
  inversion H4. subst.
  exists k.
  split.
  - assumption.
  - rewrite plus_comm.
    reflexivity.
Qed.

Lemma inspect_eval__LetNonRec_cons : forall s x T eb bs e j e_f,
    Let NonRec (TermBind s (VarDecl x T) eb :: bs) e =[j]=> e_f ->
    exists j_1 eb_f, 
      eb =[j_1]=> eb_f /\ j_1 <= j /\
      exists bs' e',
        substitute x eb_f (Let NonRec bs e) (Let NonRec bs' e') /\
        exists j_2,
          Let NonRec bs' e' =[j_2]=> e_f /\
          j_1 + 1 + j_2 = j.
Proof.
  intros.
  inversion H. subst.
  inversion H4. subst.
  exists kb, vb.
  split. auto.
  split. apply skip. (* TODO*)
  exists bs', t'.
  split. auto.
  exists k.
  split. apply E_Let. auto.
  reflexivity.
Qed.

Lemma compatibility_LetNonRec : forall bs Delta Gamma t bs' t' T,
    forall Delta' Gamma',
      (Delta', Gamma') = append (flatten (List.map binds bs)) (Delta, Gamma) ->
      LR_logically_approximate Delta' Gamma' t t' T ->
      LR_logically_approximate_bindings_nonrec Delta Gamma bs bs' ->
      LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T.
Proof.
  induction bs.
  - intros Delta Gamma t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bs.
    unfold LR_logically_approximate.

    inversion IH_LR__bs. subst.

    split. {
      eapply T_Let.
      all: eauto with typing.
      unfold LR_logically_approximate in IH_LR__t.
      apply IH_LR__t.
    }

    split. {
      eapply T_Let.
      all: eauto with typing.
      unfold LR_logically_approximate in IH_LR__t.
      apply IH_LR__t.
    }

    intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
    subst.

    intros e_msa e'_msa e_ms e'_ms.
    intros Hmsa__e_msa Hmsa__e'_msa Hms__e_ms Hms__e'_ms.

    destruct (msubstA_LetNonRec_nil _ _ _ Hmsa__e_msa) as [t_msa [Hmsa__t_msa Heq]].
    destruct (msubstA_LetNonRec_nil _ _ _ Hmsa__e'_msa) as [t'_msa [Hmsa__t'_msa Heq']].
    subst.
    destruct (msubst_LetNonRec_nil _ _ _ Hms__e_ms) as [t_ms [Hms__t_ms Heq]].
    destruct (msubst_LetNonRec_nil _ _ _ Hms__e'_ms) as [t'_ms [Hms__t'_ms Heq']].
    subst.

    autorewrite with RC.

    split. {
      replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
      - eapply msubst_preserves_typing_1; eauto.
        eapply msubstA_preserves_typing_1; eauto.
        eapply T_Let; eauto with typing. 
        eapply IH_LR__t.
      - rewrite mupd_empty; eauto.
    }
    split. {
      replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
      - eapply msubst_preserves_typing_2; eauto.
        eapply msubstA_preserves_typing_2; eauto.
        eapply T_Let; eauto with typing. 
        eapply IH_LR__t.
      - rewrite mupd_empty; eauto.
    }

    intros j Hlt__j e_f Hev__e_f.
    apply inspect_eval__LetNonRec_nil in Hev__e_f as temp.
    destruct temp as [j_1 [Hev'__e_f Heq]].
    
    destruct IH_LR__t as [_ [_ IH_LR__t]].
    assert (RC k T rho t_ms t'_ms). {
      simpl in Hbinds.
      rewrite flatten_nil in Hbinds.
      rewrite append_emptyContext_l in Hbinds.
      inversion Hbinds. subst.
      eapply IH_LR__t.
      all: eauto.
    }

    autorewrite with RC in H.
    destruct H as [_ [_ H]].

    assert (Hlt__j_1 : j_1 < k). {
      subst. 
      rewrite plus_comm in Hlt__j.
      apply Nat.succ_lt_mono.
      apply le_S.
      assumption.
    }
    remember (H j_1 Hlt__j_1 e_f Hev'__e_f).
    clear Heqe. rename e into H0.

    destruct H0 as [e'_f [j'_1 [Hev__e'_f H0]]].
    exists e'_f. exists (S j'_1).
    split. {
      eapply E_Let.
      eapply E_NilB_NonRec.
      eassumption.
    }

    assert (forall i, i < k - j -> i < k - j_1). { 
      intros.
      subst.
      rewrite plus_comm in H1.
      simpl in H1.
      apply skip. 
    }

    destruct T.
    all: eauto.
    intros.
    eapply RD_sem_syn in H2 as H3; eauto.
    destruct H3 as [T1 [T2 [Hsyn1 Hsyn2]]].
    apply H0 in H2 as H3; eauto.
    eapply RD_rel in H2; eauto.
    unfold Rel in H2.
    eapply H2; eauto.
    subst.
    apply skip.

  - intros Delta Gamma t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bbs.
    unfold LR_logically_approximate.
    rename a into b.
    remember IH_LR__t as IH_LR__t__copy.
    clear HeqIH_LR__t__copy.

    inversion IH_LR__bbs. subst.
    rename bs'0 into bs'.
    rename Delta'0 into Delta''.
    rename Gamma'0 into Gamma''.
    rename H1 into IH_LR__b.
    rename H2 into Hbinds''.
    rename H5 into Heqbinds.
    rename H7 into IH_LR__bs.

    assert (IH_LR__let : LR_logically_approximate Delta'' Gamma'' (Let NonRec bs t) (Let NonRec bs' t') T). {
      eapply IHbs.
      all: eauto.
      apply skip. (* TODO *)
    }
    remember IH_LR__let as IH_LR__let__copy.
    clear HeqIH_LR__let__copy.

    split. {
      eapply T_Let. 
      - apply Hbinds.
      - eapply LR_la_bnr__oks in IH_LR__bbs. 
        apply IH_LR__bbs. 
      - apply IH_LR__t.  
    }

    split. {
      eapply T_Let.
      - eapply LR_la_bnr__oks in IH_LR__bbs.
        destruct IH_LR__bbs as [_ [_ Heq]].
        rewrite <- Heq.
        apply Hbinds.
      - eapply LR_la_bnr__oks in IH_LR__bbs.
        apply IH_LR__bbs.
      - apply IH_LR__t.
    }

    intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
    subst.

    intros e_msa e'_msa e_ms e'_ms.
    intros Hmsa__e_msa Hmsa__e'_msa Hms__e_ms Hms__e'_ms.

    destruct (msubstA_LetNonRec_cons _ _ _ _ _ Hmsa__e_msa) as [b_msa [bs_msa [t_msa [Hmsa__b_msa [Hmsa__eih_msa Heq]]]]].
    destruct (msubstA_LetNonRec_cons _ _ _ _ _ Hmsa__e'_msa) as [b'_msa [bs'_msa [t'_msa [Hmsa__b'_msa [Hmsa__eih'_msa Heq']]]]].
    subst.

    destruct (msubst_LetNonRec_cons _ _ _ _ _ Hms__e_ms) as [b_ms [bs_ms [t_ms [Hms__b_ms [Hms__eih_ms Heq]]]]].
    destruct (msubst_LetNonRec_cons _ _ _ _ _ Hms__e'_ms) as [b'_ms [bs'_ms [t'_ms [Hms__b'_ms [Hms__eih'_ms Heq']]]]].
    subst.

    autorewrite with RC.
    split. {
      replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
      - eapply msubst_preserves_typing_1; eauto.
        eapply msubstA_preserves_typing_1; eauto.
        eapply T_Let; eauto.
        + eapply LR_la_bnr__oks in IH_LR__bbs. 
          apply IH_LR__bbs.
        + eapply IH_LR__t.
      - rewrite mupd_empty; eauto.
    }
    split. {
      replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
      - eapply LR_la_bnr__oks in IH_LR__bbs as H.
        eapply msubst_preserves_typing_2; eauto.
        eapply msubstA_preserves_typing_2; eauto.
        eapply T_Let; eauto.
        + apply H.
        + destruct H. destruct H0. 
          rewrite <- H1.
          unfold LR_logically_approximate in IH_LR__t.
          inversion Hbinds. subst.
          apply IH_LR__t.
      - rewrite mupd_empty; eauto.
    }

    assert (H_RB : RB k rho b_ms b'_ms) by (eapply IH_LR__b; eauto).
    autorewrite with RB in H_RB.

    destruct b, b'.
    + destruct v.
      rename s into stricty.
      rename s1 into x.
      rename t2 into Tb.
      rename t0 into eb.
    
      destruct v0.
      rename s0 into stricty'.
      rename s into x'.
      rename t0 into Tb'.
      rename t1 into eb'.
      
      assert (x' = x /\ Tb' = Tb). {
        inversion Heqbinds.
        apply skip.
      }

      destruct H.
      subst.

      destruct (msubstA_TermBind _ _ _ _ _ _ Hmsa__b_msa) as [eb_msa [Hmsa__eb_msa Heq]].
      destruct (msubstA_TermBind _ _ _ _ _ _ Hmsa__b'_msa) as [eb'_msa [Hmsa__eb'_msa Heq']].
      subst.
      destruct (msubst_TermBind _ _ _ _ _ _ Hms__b_ms) as [eb_ms [Hms__eb_ms Heq]].
      destruct (msubst_TermBind _ _ _ _ _ _ Hms__b'_ms) as [eb'_ms [Hms__eb'_ms Heq']].
      subst.

      intros j Hlt__j e_f Hev__e_f.
      apply inspect_eval__LetNonRec_cons in Hev__e_f as temp.
      destruct temp as [j_1 [eb_f [Hev__eb_f [Hle__j_1 [bs0 [t0 [Hsubs__ih [j_2 [Hev__ih Heq]]]]]]]]].
      
      
      destruct H_RB as [_ [ _ H_RC]].
      autorewrite with RC in H_RC.

      destruct H_RC as [_ [_ H_RC]].
      assert (Hlt__j_1 : j_1 < k). { apply skip. }
      remember (H_RC j_1 Hlt__j_1 eb_f Hev__eb_f).
      clear Heqe. clear H_RC. rename e into H_RC.

      destruct H_RC as [eb'_f [j'_1 [Hev__eb'_f H_RC]]].
      clear H_RC.

      simpl in Hms__eih_ms.
      assert (msubst_term ((x, eb_f) :: env) (Let NonRec bs_msa t_msa) (Let NonRec bs0 t0)). {
        apply skip.
      }
      simpl in Hms__eih'_ms.
      assert (exists bs0' t0', substitute x eb'_f (Let NonRec bs'_ms t'_ms) (Let NonRec bs0' t0')). {
        apply skip.
      }
      destruct H0 as [bs0' [t0' H1]].
      assert (msubst_term ((x, eb'_f) :: env') (Let NonRec bs'_msa t'_msa) (Let NonRec bs0' t0')). {
        apply skip.
      }
       
      destruct IH_LR__let as [_ [_ IH_LR__let]].
      assert (RC k T rho (Let NonRec bs0 t0) (Let NonRec bs0' t0')). {
        eapply IH_LR__let.
        - apply skip.
        - apply skip.
        - split. eassumption.
          eapply RG_cons. 
          all: apply skip.
        - eassumption.
        - eassumption.
        - eassumption.
        - eassumption.
      }

      autorewrite with RC in H2.
      destruct H2 as [_ [_ H2]].
      assert (Hlt__j_2 : j_2 < k). {  apply skip. }
      remember (H2 _ Hlt__j_2 _ Hev__ih).
      clear Heqe. clear H2. rename e into H2.
      destruct H2 as [e'_f [j'_2 [Hev__e'_f H2]]].

      eexists. eexists.
      split. {
        eapply E_Let.
        eapply E_ConsB_NonRec.
        all: eauto.
        inversion Hev__e'_f.
        subst.
        eauto.
      }

      assert (forall i, i < k - j -> i < k - j_2). { apply skip. } 

      destruct T.
      all: eauto.
      apply skip.
    +
Admitted.