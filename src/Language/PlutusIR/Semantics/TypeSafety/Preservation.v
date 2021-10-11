Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.


Lemma preservation__compute_defaultfun : forall t T,
    empty ,, empty |-+ t : T ->
    forall v,
      compute_defaultfun t = Datatypes.Some v ->
      empty ,, empty |-+ v : T.
Proof with (try discriminate).
  intros.
  destruct t...
  simpl in H0.
  destruct d...
  all: destruct l...
  all: destruct t...
  all: destruct s...
  all: destruct u...
  all: destruct v0...
  all: destruct l...
  all: try destruct t...
  all: try destruct s...
  all: try destruct u0...
  all: try destruct v0...
  all: try destruct l...
  all: try solve [inversion H0; subst; inversion H; subst; inversion H4; subst; simpl; eauto with typing].
  destruct t...
  destruct s...
  destruct u1...
  destruct v0...
  destruct l...
  try solve [inversion H0; subst; inversion H; subst; inversion H4; subst; simpl; eauto with typing].
Qed.




Definition P_eval (t v : Term) (k : nat) :=
  forall T,
    empty ,, empty |-+ t : T ->
    empty ,, empty |-+ v : T.

    
Definition P_eval_bindings_nonrec (t v : Term) (k : nat) :=
  forall bs t0,
    t = Let NonRec bs t0 ->
    forall T,
      empty ,, empty |-+ t : T ->
      empty ,, empty |-+ v : T.

Definition P_eval_bindings_rec (bs0 : list Binding) (t v : Term) (k : nat) :=
  (mupdate empty (flatten (List.map binds_Delta bs0))) ,, (mupdate empty (flatten (List.map binds_Gamma bs0))) |-oks_r bs0 ->
  forall bs t0,
    t = Let Rec bs t0 ->
    forall T,
      empty ,, empty |-+ t : T ->
      empty ,, empty |-+ v : T.


Axiom skip : forall P, P.

Theorem preservation : 
  (forall (t v : Term) (j : nat), t =[j]=> v -> P_eval t v j) /\
  (forall (t v : Term) (j : nat), eval_bindings_nonrec t v j -> P_eval_bindings_nonrec t v j) /\
  (forall (bs0 : list Binding) (t v : Term) (j : nat), eval_bindings_rec bs0 t v j -> P_eval_bindings_rec bs0 t v j). 
Proof.
  apply eval__multind with
    (P := P_eval)
    (P0 := P_eval_bindings_nonrec)
    (P1 := P_eval_bindings_rec).
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
    inversion H1. subst.
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
    eapply H0 in H10.
    inversion H10. subst.
    eauto.
  - (* E_Constant *) 
    intros. unfold P_eval. intros.
    assumption.
  - (* E_Builtin *)
    intros. unfold P_eval. intros.
    inversion H0. subst.
    destruct f; simpl.
    all: eapply T_ExtBuiltin; simpl; eauto.
    all: intros; exfalso; eauto.
  - (* E_ExtBuiltinPartiallyApplied *) 
    intros. unfold P_eval. intros.
    assumption.
  - (* E_ExtBuiltinFullApplied *)
    intros. unfold P_eval. intros.
    eapply preservation__compute_defaultfun; eauto.
  - (* E_ApplyExtBuiltin *) 
    intros. unfold P_eval. intros.
    inversion H5. subst.
    eapply H0 in H10; eauto.
    inversion H10. subst.
    unfold combineTy in H16.
    apply skip.

  - (* E_If *)
    intros. unfold P_eval. intros.
    assumption.
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
    apply H0 in H8.
    apply H2.
    
    apply skip. (* TODO *)
  - (* E_IfFalse *)
    intros. unfold P_eval. intros.
    inversion H3. subst.
    apply H0 in H8.
    apply H2.

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
    simpl in H11.
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
        -- reflexivity.
        -- inversion H11. subst.
           simpl in H10.
           apply H10.
        -- simpl in H13.
           unfold flatten in H13.
           simpl in H13.
           rewrite List.concat_app in H13.
           rewrite List.concat_app in H13.
           simpl in H13.
           rewrite mupdate_app in H13.
           rewrite mupdate_app in H13.
           simpl in H13.
           apply H13.
      * inversion H11. subst.
        inversion H9. subst.
        apply H0.
        apply H16.

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
        -- reflexivity.
        -- inversion H10. subst.
           simpl in H9.
           unfold flatten in H9.
           simpl in H9.
           rewrite List.concat_app in H9.
           rewrite List.concat_app in H9.
           simpl in H9.
           rewrite mupdate_app in H9.
           rewrite mupdate_app in H9.
           simpl in H9.
           apply H9.
        -- simpl in H12.
           unfold flatten in H12.
           simpl in H12.
           rewrite List.concat_app in H12.
           rewrite List.concat_app in H12.
           simpl in H12.
           rewrite mupdate_app in H12.
           rewrite mupdate_app in H12.
           simpl in H12.
           apply H12.
      * eapply T_LetRec.
        -- reflexivity.
        -- reflexivity.
        --  apply H1.
        -- apply skip.
Abort.

Theorem preservation : forall t v j T,
    empty ,, empty |-+ t : T ->
    t =[j]=> v ->
    empty ,, empty |-+ v : T.
Proof. Admitted.