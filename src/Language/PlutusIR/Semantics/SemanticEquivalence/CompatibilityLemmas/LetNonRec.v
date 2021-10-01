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

(*
Lemma subst_bs_nr__bound_vars : forall x s bs bs',
    substitute_bindings_nonrec x s bs bs' ->
    term_vars_bound_by_bindings bs = term_vars_bound_by_bindings bs'.
Proof.
  intros.
  induction H.
  - reflexivity.
  - destruct b. 
    all: inversion H0; subst.
    all: auto.
  - destruct b.
    all: inversion H0. subst.
    all: unfold term_vars_bound_by_bindings.
    all: simpl.
    all: f_equal.
    all: auto.
Qed.*)

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
    
(*
Lemma msubst_LetNonRec : forall ss bs e t',
    msubst_term ss (Let NonRec bs e) t' ->
    exists bs' e', 
      ForallP (fun b => exists b, msubst )
      msubst_bindings_nonrec ss bs bs' /\ 
      msubst_term (mdrop (term_vars_bound_by_bindings bs) ss) e e' /\ 
      t' = Let NonRec bs' e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists bs, e.
    rewrite mdrop_nil.
    eauto using msubst_bindings_nonrec__nil, msubst_nil, msubst_cons. 
  - inversion H. subst.
    rename t'0 into e''.
    inversion H2.
    + subst.
      apply IHss in H5.
      destruct H5 as [bs'' [e'' [H9 [H10 H11]]]].
      subst.
      exists bs'', e''.
      split. {
        apply msubst_bindings_nonrec__cons with bs'.
        + assumption.
        + apply H9.
      }
      split. {
        rewrite In__mdrop; auto.
        erewrite subst_bs_nr__bound_vars; eauto.
      }
      reflexivity.
    + subst.
      rename t0' into e'.
      apply IHss in H5.
      destruct H5 as [bs'' [e'' [H10 [H11 H12]]]].
      subst.
      exists bs'', e''.
      split. {
        apply msubst_bindings_nonrec__cons with bs'.
        + assumption.
        + apply H10.
      }
      split. {
        rewrite not_In__mdrop; auto.
        eapply msubst_cons; eauto. 
        erewrite subst_bs_nr__bound_vars; eauto.
      }
      reflexivity.
Qed.

Lemma msubstA_LetNonRec : forall ss bs e t',
    msubstA ss (Let NonRec bs e) t' ->
    exists bs' e', 
      msubstA_bindings_nonrec ss bs bs' /\ 
      msubstA (mdrop (tyvars_bound_by_bindings bs) ss) e e' /\ 
      t' = Let NonRec bs' e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists bs, e.
    rewrite mdrop_nil.
    eauto using msubstA_bindings_nonrec__nil, msubstA_nil, msubstA_cons. 
  - inversion H. subst.
    rename t'0 into e''.
    inversion H2.
    + subst.
      apply IHss in H5.
      destruct H5 as [bs'' [e'' [H9 [H10 H11]]]].
      subst.
      exists bs'', e''.
      split. {
        apply msubstA_bindings_nonrec__cons with bs'.
        + assumption.
        + apply H9.
      }
      split. {
        rewrite In__mdrop; auto.
        erewrite substA_bs_nr__bound_tyvars; eauto.
      }
      reflexivity.
    + subst.
      rename t0' into e'.
      apply IHss in H5.
      destruct H5 as [bs'' [e'' [H10 [H11 H12]]]].
      subst.
      exists bs'', e''.
      split. {
        apply msubstA_bindings_nonrec__cons with bs'.
        + assumption.
        + apply H10.
      }
      split. {
        rewrite not_In__mdrop; auto.
        eapply msubstA_cons; eauto. 
        erewrite substA_bs_nr__bound_tyvars; eauto.
      }
      reflexivity.
Qed. *)

Lemma compatibility_LetNonRec : forall Delta Gamma bs t bs' t' T,
    forall Delta' Gamma',
      (Delta', Gamma') = append (flatten (List.map binds bs)) (Delta, Gamma) ->
      LR_logically_approximate Delta' Gamma' t t' T ->
      LR_logically_approximate_bindings_nonrec Delta Gamma bs bs' ->
      LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T.
Proof.
  intros Delta Gamma bs t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bs.
  unfold LR_logically_approximate.

  split. {
    eapply T_Let. 
    - apply Hbinds.
    - eapply LR_la_bnr__oks in IH_LR__bs. 
      apply IH_LR__bs. 
    - apply IH_LR__t.  
  }

  split. {
    eapply T_Let.
    - eapply LR_la_bnr__oks in IH_LR__bs.
      destruct IH_LR__bs as [_ [_ Heq]].
      rewrite <- Heq.
      apply Hbinds.
    - eapply LR_la_bnr__oks in IH_LR__bs.
      apply IH_LR__bs.
    - apply IH_LR__t.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  (*
  destruct (msubstA_LetNonRec _ _ _ _ HmsA__e_msa) as [bs_msa [t_msa [HmsA__bs_msa [HmsA__t_msa Heq]]]].
  destruct (msubstA_LetNonRec _ _ _ _ HmsA__e'_msa) as [bs'_msa [t'_msa [HmsA__bs'_msa [HmsA__t'_msa Heq']]]].
  subst.
  destruct (msubst_LetNonRec _ _ _ _ Hms__e_ms) as [bs_ms [t_ms [Hms__bs_ms [Hms__t_ms Heq]]]].
  destruct (msubst_LetNonRec _ _ _ _ Hms__e'_ms) as [bs'_ms [t'_ms [Hms__bs'_ms [Hms__t'_ms Heq']]]].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      eapply T_Let; eauto.
      + eapply LR_la_bnr__oks in IH_LR__bs. 
        apply IH_LR__bs.
      + eapply IH_LR__t.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply LR_la_bnr__oks in IH_LR__bs as H.
      eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      eapply T_Let; eauto.
      + apply H.
      + destruct H. destruct H0. 
        rewrite <- H1.
        Fail rewrite <- Hbinds. (* why?? *)
        unfold LR_logically_approximate in IH_LR__t.
        apply skip.
    - rewrite mupd_empty; eauto.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  inversion H3. subst.
  - unfold LR_logically_approximate in IH_LR__t.
    destruct IH_LR__t as [_ [_ IH_LR__t]].
    inversion Hbinds. subst. 
  *)
Admitted.