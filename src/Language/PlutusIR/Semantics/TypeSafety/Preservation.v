Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.


Lemma preservation__compute_defaultfun : forall t T,
    emptyContext |-+ t : T ->
    forall v,
      compute_defaultfun t = Datatypes.Some v ->
      emptyContext |-+ v : T.
Proof.
  intros.
  destruct t; inversion H0.
  destruct t1; inversion H0. {
    destruct t1_1; inversion H0. {
      destruct t1_1_1; inversion H0. 
      destruct d; inversion H0.
      destruct t1_1_2; inversion H0.
      destruct s; inversion H0.
      destruct u; inversion H0.
      destruct v0; inversion H0.
      destruct t1_2; inversion H0.
      destruct s; inversion H0.
      destruct u0; inversion H0.
      destruct v0; inversion H0.
      destruct t2; inversion H0.
      destruct s; inversion H0.
      destruct u1; inversion H0.
      destruct v0; inversion H0.
      inversion H. subst.
      inversion H23; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H20.
      subst.
      inversion H21; subst.
      inversion H24; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H22.
      subst.
      inversion H20; subst.
      inversion H26; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H25.
      subst.
      inversion H22; subst.
      apply T_Constant.
    } {
      destruct d; inversion H2; 
        try solve [
          destruct t1_2; inversion H2;
          destruct s; inversion H2;
          destruct u; inversion H2;
          destruct v0; inversion H0;
          destruct t2; inversion H0;
          destruct s; inversion H0;
          destruct u0; inversion H0;
          destruct v0; inversion H0;
          inversion H13; subst;
          inversion H; subst;
          clear H;
          inversion H16; subst;
          clear H16;
          inversion H18; subst;
          clear H18;
          inversion H15; subst;
          clear H15;
          inversion H19; subst;
          clear H19;
          apply Eqdep.EqdepTheory.inj_pair2 in H16;
          subst;
          apply Eqdep.EqdepTheory.inj_pair2 in H15;
          subst;
          apply T_Constant
        ].
      }
    } {
      destruct d; inversion H2;
      destruct t2; inversion H2;
      destruct s; inversion H2;
      destruct u; inversion H2;
      destruct v0; inversion H2;
      inversion H; subst;
      inversion H11; subst;
      inversion H11; subst;
      apply T_Constant.
    }
Qed.




Definition P_eval (t v : Term) (k : nat) :=
  forall T,
    emptyContext |-+ t : T ->
    emptyContext |-+ v : T.

    
Definition P_eval_bindings_nonrec (t v : Term) (k : nat) :=
  forall bs t0,
    t = Let NonRec bs t0 ->
    forall T,
      emptyContext |-+ t : T ->
      emptyContext |-+ v : T.

Definition P_eval_bindings_rec (bs0 : list Binding) (t v : Term) (k : nat) :=
  flatten (List.map binds bs0) |-oks_r bs0 ->
  forall bs t0,
    t = Let Rec bs t0 ->
    forall T,
      emptyContext |-+ t : T ->
      emptyContext |-+ v : T.


Axiom skip : forall P, P.

Theorem preservation : 
  (forall (t v : Term) (k : nat), t =[k]=> v -> P_eval t v k) /\
  (forall (t v : Term) (k : nat), eval_bindings_nonrec t v k -> P_eval_bindings_nonrec t v k) /\
  (forall (bs0 : list Binding) (t v : Term) (k : nat), eval_bindings_rec bs0 t v k -> P_eval_bindings_rec bs0 t v k). 
Proof.
  apply eval__multind with
    (P := P_eval)
    (P0 := P_eval_bindings_nonrec)
    (P1 := P_eval_bindings_rec).
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
    + inversion H1. subst.
      rewrite append_emptyContext_r in H6.
      assumption.
  - (* E_TyAbs *)
    intros. unfold P_eval. intros.
    assumption.
  - (* E_LamAbs *)
    intros. unfold P_eval. intros.
    assumption. 
  - (* E_Apply *) 
    intros. unfold P_eval. intros.
    inversion H5. subst.
    eapply H4.
    eapply substitution_preserves_typing__Term; eauto.
    eapply H0 in H9.
    inversion H9. subst.
    eauto.
  - (* E_Constant *) 
    intros. unfold P_eval. intros.
    assumption.
  - (* E_Builtin *) 
    intros. unfold P_eval. intros.
    assumption.
  - (* E_ApplyBuiltin1 *) 
    intros. unfold P_eval. intros.
    inversion H5. subst.
    apply T_Apply with T1.
    + apply H0.
      assumption. 
    + apply H3.
      assumption.
  - (* E_ApplyBuiltin2 *) 
    intros. unfold P_eval. intros.
    inversion H6. subst.
    eapply preservation__compute_defaultfun.
    + apply T_Apply with T1. 
      * apply H0.
        assumption.
      * apply H3.
        assumption.
    + assumption.
  - (* E_IfTyInst *) 
    intros. unfold P_eval. intros.
    inversion H1; subst.
    eapply T_TyInst; eauto.
  - (* E_IfCondition *)
    intros. unfold P_eval. intros.
    inversion H3; subst.
    eapply T_Apply; eauto.
  - (* E_IfThenBranch *)
    intros. unfold P_eval. intros.
    inversion H1; subst.
    eapply T_Apply; eauto.
  - (* E_IfTrue *) 
    intros. unfold P_eval. intros.
    inversion H3; subst.
    apply H0 in H7.
    apply H2.

    inversion H7. subst.
    inversion H8. subst.
    inversion H10; subst.
    inversion H6. subst.
    
    apply skip. (* TODO *)
  - (* E_IfFalse *)
    intros. unfold P_eval. intros.
    inversion H3. subst.
    apply H0 in H7.
    apply H2.

    inversion H7. subst.
    inversion H8. subst.
    inversion H10. subst.
    inversion H6. subst.

    apply skip. (* TODO *)
  - (* E_TyInst *) 
    intros. unfold P_eval. intros.
    inversion H3. subst.
    apply skip.

  - (* E_Error *)
    intros. unfold P_eval. intros.
    assumption.
  - (* E_IWrap *) 
    intros. unfold P_eval. intros.
    inversion H1. subst.
    eapply T_IWrap; eauto.
  - (* E_Unwrap *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    unfold P_eval in H0.
    apply H0 in H3.
    inversion H3. subst.
    assert (K = K0) by eauto using unique_kinds.
    subst.
    apply skip. (* TODO *)

  - (* E_NilB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H1. subst.
    inversion H2. subst.
    simpl in H9.
    rewrite flatten_nil in H9.
    rewrite append_emptyContext_l in H9.
    apply H0.
    assumption.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H4. subst.
    inversion H3. subst.
    eapply H2.
    + reflexivity.
    + eapply substitution_preserves_typing__Term.
      * eapply T_Let.
        -- reflexivity.
        -- inversion H9. subst.
           simpl in H10.
           rewrite append_emptyContext_r in H10.
           apply H10.
        -- simpl in H11.
           rewrite flatten_extract in H11.
           rewrite append_emptyContext_r in H11.
           apply H11.
      * inversion H9. subst.
        inversion H8. subst.
        apply H0.
        apply H15.

  - (* E_NilB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H2. subst.
    apply H0.
    inversion H3. subst.
    assumption.
  - (* E_ConsB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H3. subst.
    inversion H2. subst.    
    eapply H0. 
    + assumption.
    + simpl. apply skip.
    + eapply substitution_preserves_typing__Term.
      * eapply T_LetRec.
        -- reflexivity.
        -- inversion H8. subst.
           simpl in H9.
           rewrite flatten_extract in H9.
           rewrite append_emptyContext_r in H9.
           apply H9.
        -- inversion H8. subst.
           simpl in H10.
           rewrite flatten_extract in H10.
           rewrite append_emptyContext_r in H10.
           apply H10.
      * eapply T_LetRec.
        -- reflexivity.
        -- rewrite append_emptyContext_r. 
           apply H1.
        -- rewrite append_emptyContext_r.
           rewrite append_emptyContext_r in H10.
           rewrite append_emptyContext_r in H8.
           inversion H8. subst.
           inversion H7. subst.
           eapply context_invariance.
           ++ apply H14.
           ++ intros.
              apply skip.
           ++ intros.
              apply skip.
Abort.

Theorem preservation : forall t v k T,
    emptyContext |-+ t : T ->
    t =[k]=> v ->
    emptyContext |-+ v : T.
Proof. Admitted.