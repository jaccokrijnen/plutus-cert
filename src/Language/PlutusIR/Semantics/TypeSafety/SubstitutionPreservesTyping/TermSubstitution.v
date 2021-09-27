Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.

Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma append_extendT_shadow : forall ctx' x T U ctx,
    lookupT ctx' x = Datatypes.Some T ->
    Implementations.append ctx' (x |T-> U; ctx) = Implementations.append ctx' ctx.
Proof.
  intros.
  unfold Implementations.append.
  apply cong_eq.
  - reflexivity.
  - apply functional_extensionality.
    intros.
    simpl.
    destruct (lookupT ctx' x0) eqn:Hx0.
    + reflexivity.
    + assert (forall ctx' x x0, lookupT ctx' x = Datatypes.Some T -> lookupT ctx' x0 = None -> x <> x0). {
        intros.
        intros Hcon.
        subst.
        rewrite H0 in H1.
        inversion H1.
      }
      remember (H0 _ _ _ H Hx0).
      clear Heqn.
      rewrite update_neq; auto.
Qed.

Lemma append_extendT_permute : forall ctx' x U ctx,
    lookupT ctx' x = None ->
    Implementations.append ctx' (x |T-> U; ctx) = (x |T-> U; Implementations.append ctx' ctx).
Proof. 
  intros.
  unfold Implementations.append.
  apply cong_eq.
  - reflexivity.
  - apply functional_extensionality.
    intros.
    simpl.
    destruct (lookupT ctx' x0) eqn:Hx0.
    + assert (forall ctx' x x0 T, lookupT ctx' x = Datatypes.Some T -> lookupT ctx' x0 = None -> x <> x0). {
        intros.
        intros Hcon.
        subst.
        rewrite H0 in H1.
        inversion H1.
      }
      remember (H0 _ _ _ _ Hx0 H).
      clear Heqn.
      rewrite update_neq; auto.
      rewrite Hx0.
      reflexivity.
    + destruct (x =? x0) eqn:Heqb.
      * apply eqb_eq in Heqb as Heq.
        subst.
        rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * apply eqb_neq in Heqb as Hneq.
        rewrite update_neq; auto.
        rewrite update_neq; auto.
        rewrite Hx0.
        reflexivity.
Qed.


Lemma binds_binds_bound_vars : forall a x,
    List.In x (term_vars_bound_by_binding a) ->
    exists U, lookupT (binds a) x = Datatypes.Some U.
Proof.
  intros.
  destruct a.
  - simpl.
    destruct (getName v =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exists (getTy v).
      apply update_eq.
    + apply eqb_neq in Heqb as Hneq.
      simpl in H.
      destruct v.
      simpl in H.
      destruct H.
      * apply Hneq in H.
        destruct H.
      * destruct H.
  - simpl in H.
    destruct t.
    inversion H.
  - simpl.
Admitted.

Lemma mapbinds_binds_bound_vars : forall bs x,
  List.In x (term_vars_bound_by_bindings bs) ->
  exists U, lookupT (flatten (List.map binds bs)) x = Datatypes.Some U.
Proof.
  induction bs.
  - intros.
    inversion H.
  - intros.
    unfold term_vars_bound_by_bindings in H.
    simpl in H.
    apply List.in_app_or in H.
    destruct H.
    + simpl.
      unfold flatten.
      simpl.
      rewrite concat_append.
      simpl. 
      destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x).
      * exists t.
        reflexivity.
      * destruct (lookupT (binds a) x) eqn:Hlookup.
        -- exists t.
           reflexivity.
        -- apply binds_binds_bound_vars in H.
           destruct H. 
           rewrite H in Hlookup.
           inversion Hlookup.
    + simpl.
      unfold flatten.
      simpl.
      rewrite concat_append.
      simpl.
      destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x) eqn:Hlookup.
      * exists t.
        reflexivity.
      * apply IHbs in H.
        destruct H.
        unfold flatten in H.
        rewrite H in Hlookup.
        inversion Hlookup.
Qed.

Lemma binds_unbinds_unbound_vars : forall a x,
    ~(List.In x (term_vars_bound_by_binding a)) ->
    lookupT (binds a) x = None.
Proof.
  intros.
  destruct a.
  - simpl.
    destruct (getName v =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      destruct v.
      exfalso.
      apply H.
      simpl.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      apply update_neq.
      assumption.
  - reflexivity.
  - simpl.
    destruct d.
    simpl.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exfalso.
      apply H.
      simpl.
      destruct t.
      simpl.
      left.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_neq; auto.
      destruct  (lookupT
      (List.fold_right Implementations.append emptyContext
         (List.map
            (fun x0 : binderTyname * Ty => fst x0 |T-> snd x0; emptyContext)
            (List.map (constrBind (Datatype t l s l0)) l0))) x) eqn:E.
      * exfalso.
        apply H.
        simpl.
        destruct t.
        simpl.
        right.
Admitted.

Lemma mapbinds_unbinds_unbound_vars : forall bs x,
    ~(List.In x (term_vars_bound_by_bindings bs)) ->
    lookupT (flatten (List.map binds bs)) x = None.
Proof.
  induction bs.
  - intros.
    reflexivity.
  - intros.
    simpl.
    unfold flatten.
    simpl.
    rewrite concat_append.
    simpl.
    destruct (lookupT (Implementations.concat (List.rev (List.map binds bs))) x) eqn:Hlookup.
    + rewrite IHbs in Hlookup.
      * symmetry in Hlookup.
        assumption.
      * intros Hcon.
        apply H.
        unfold term_vars_bound_by_bindings.
        simpl.
        apply List.in_or_app.
        right.
        assumption.
    + destruct (lookupT (binds a) x) eqn:Hlookup'.
      * rewrite binds_unbinds_unbound_vars in Hlookup'.
        -- auto.
        -- intros Hcon.
           apply H.
           unfold term_vars_bound_by_bindings.
           simpl.
           apply List.in_or_app.
           left.
           assumption.
      * reflexivity.
Qed.

Lemma context_invariance_T__constructor_well_formed : forall ctx_T' ctx_T ctx_K c ,
  (ctx_K, ctx_T) |-ok_c c ->
  (ctx_K, ctx_T') |-ok_c c.
Proof.
  intros.
  inversion H. subst.
  apply W_Con.
  intros.
  apply H0.
  assumption.
Qed.

Definition P_Term (t : Term) :=
  forall ctx x U v T t',
    extendT x U ctx |-+ t : T ->
    emptyContext |-+ v : U ->
    substitute x v t t' ->
    ctx |-+ t' : T.
#[export] Hint Unfold P_Term : core.

Definition P_Binding (b : Binding) : Prop :=
  forall ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
#[export] Hint Unfold P_Binding : core.

Definition P_Bindings_NonRec (bs : list Binding) : Prop :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_nr bs ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute_bindings_nonrec x v bs bs' ->
    ctx |-oks_nr bs' /\ List.map binds bs = List.map binds bs'.

Definition P_Bindings_Rec (bs : list Binding) : Prop :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_r bs ->
    emptyContext |-+ v : U ->
    Util.ForallP P_Binding bs ->
    substitute_bindings_rec x v bs bs' ->
    ctx |-oks_r bs' /\ List.map binds bs = List.map binds bs'.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H2. subst.
    auto with typing.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H2.
    + subst.
      split.
      * apply W_ConsB_NonRec.
        -- apply Util.ForallP_hd in H1.
           unfold P_Binding in H1.
           eapply H1.
           ++ inversion H. subst.
              apply H6.
           ++ apply H0.
           ++ assumption.
        -- apply Util.ForallP_hd in H1.
           unfold P_Binding in H1.
           inversion H. subst.
           destruct (H1 _ _ _ _ _ H6 H0 H9).
           rewrite <- H4.
           apply binds_binds_bound_vars in H7.
           destruct H7.
           erewrite append_extendT_shadow in H8; eauto.
      * simpl.
        apply Util.ForallP_hd in H1.
        inversion H. subst.
        assert (binds a = binds b'). {
          eapply H1; eauto.
        }
        subst.
        f_equal; auto.
    + subst.
      split.
      * apply W_ConsB_NonRec.
        -- apply Util.ForallP_hd in H1.
           apply H1 with x U v.
           ++ inversion H. subst.
              assumption.
           ++ assumption.
           ++ assumption.
        -- apply Util.ForallP_hd in H1 as H11.
           unfold P_Binding in H11.
           inversion H. subst.
           destruct (H11 _ _ _ _ _ H7 H0 H8).
           rewrite <- H4.
           eapply IHbs.
           ++ rewrite append_extendT_permute in H9; eauto.
              apply binds_unbinds_unbound_vars; auto.
           ++ apply H0.
           ++ apply Util.ForallP_tl in H1. assumption.
           ++ apply H10.
      * simpl.
        apply Util.ForallP_hd in H1 as H11.
        inversion H. subst.
        assert (binds a = binds b'). {
          eapply H11; eauto.
        }
        f_equal; auto.
        eapply IHbs; eauto.
        -- rewrite append_extendT_permute in H9; eauto.
           apply binds_unbinds_unbound_vars; eauto.
        -- eapply Util.ForallP_tl. eauto.
Qed.

Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec.
    intros.
    inversion H2. subst.
    auto with typing.
  - unfold P_Bindings_Rec.
    intros.
    inversion H2.
    + subst.
      split.
      * apply W_ConsB_Rec.
        -- apply Util.ForallP_hd in H1.
           unfold P_Binding in H1.
           eapply H1.
           ++ inversion H. subst.
              apply H6.
           ++ apply H0.
           ++ assumption.
        -- apply Util.ForallP_tl in H1.
           eapply IHbs; eauto.
           inversion H. subst.
           auto.
      * simpl.
        inversion H. subst.
        f_equal.
        -- assert (binds a = binds b'). {
            apply Util.ForallP_hd in H1.
             eapply H1; eauto.
           }
           subst.
           auto.
        -- apply Util.ForallP_tl in H1.
           eapply IHbs; eauto.
Qed.

Lemma substitution_preserves_typing : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof.
  intros.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  - intros. autounfold. intros.
    inversion H3.
    + subst.
      eapply T_Let.
      * reflexivity.
      * eapply P_Bindings_NonRec__holds_definitionally.
        -- inversion H1. subst.
            eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * inversion H1. subst.
        assert (List.map binds bs = List.map binds bs'). {
          eapply P_Bindings_NonRec__holds_definitionally.
          -- inversion H1. subst.
             eauto.
          -- eauto.
          -- eauto.
          -- eauto.
        }
        rewrite <- H4.
        apply mapbinds_binds_bound_vars in H10.
        destruct H10. 
        erewrite append_extendT_shadow in H12.
        -- assumption.
        -- apply H5.
    + subst.
      inversion H1. subst.
      eapply T_Let.
      * reflexivity.
      * eapply P_Bindings_NonRec__holds_definitionally.
        -- eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * assert (List.map binds bs = List.map binds bs'). {
          eapply P_Bindings_NonRec__holds_definitionally.
          -- eauto.
          -- eauto.
          -- eauto.
          -- eauto.
        }
        rewrite <- H4.
        apply mapbinds_unbinds_unbound_vars in H9 as H14.
        rewrite append_extendT_permute in H13; auto.
        eapply H0; eauto.
    + subst.
      inversion H1. subst.
      eapply T_LetRec.
      * reflexivity.
      * apply mapbinds_binds_bound_vars in H10 as H12. 
        destruct H12.
        erewrite append_extendT_shadow in H8; eauto.
      * apply mapbinds_binds_bound_vars in H10 as H12. 
        destruct H12.
        erewrite append_extendT_shadow in H11; eauto.
    + subst.
      inversion H1. subst.
      eapply T_LetRec.
      * reflexivity.
      * apply mapbinds_unbinds_unbound_vars in H9 as H14.
        rewrite append_extendT_permute in H13; auto.
        rewrite append_extendT_permute in H8; auto.
        assert (List.map binds bs = List.map binds bs'). {
          eapply P_Bindings_Rec__holds_definitionally.
          -- eauto.
          -- eauto.
          -- eauto.
          -- eauto.
        }
        rewrite <- H4.
        eapply (P_Bindings_Rec__holds_definitionally bs); eauto.
      * apply mapbinds_unbinds_unbound_vars in H9 as H14.
        rewrite append_extendT_permute in H13; auto.
        rewrite append_extendT_permute in H8; auto.
        assert (List.map binds bs = List.map binds bs'). {
          eapply P_Bindings_Rec__holds_definitionally.
          -- eauto.
          -- eauto.
          -- eauto.
          -- eauto.
        }
        rewrite <- H4.
        eapply H0; eauto.
  - intros. autounfold. intros.
    inversion H1.
    + subst.
      inversion H.
      subst.
      inversion H4.
      rewrite update_eq in H3.
      inversion H3. subst. 
      eapply weakening_empty; eauto.
    + subst.
      apply T_Var.
      inversion H.
      subst.
      simpl in H4.
      rewrite update_neq in H4; auto.
  - (* TyAbs *) 
    intros. autounfold. intros.
    inversion H2. subst.
    inversion H0. subst.
    apply T_TyAbs.
    rewrite extendT_extendK_permute in H8.
    eapply H.
    + eauto.
    + eauto.
    + eauto.
  - (* LamAbs *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2.
    + subst.
      apply T_LamAbs.
      * rewrite extendT_shadow in H8.
        assumption.
      * destruct ctx.
        eauto.
    + subst.
      apply T_LamAbs.
      * eapply H.
        -- rewrite extendT_permute in H8; auto.
           apply H8.
        -- eassumption.
        -- assumption.
      * destruct ctx.
        eauto.
  - (* Apply *)
    intros. autounfold. intros.
    inversion H1. subst.
    inversion H3. subst.
    eapply T_Apply.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + eapply H0.
      * eassumption.
      * eassumption.
      * assumption.
  - (* Constant *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Constant.
  - (* Builtin *) 
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Builtin.
  - (* TyInst *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_TyInst.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + destruct ctx.
      eauto.
    + eassumption.
    + eassumption.
  - (* Error *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Error.
    destruct ctx.
    eauto.
  - (* IWrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_IWrap.
    + eassumption.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + destruct ctx.
      eauto.
    + destruct ctx.
      eauto.
  - (* Unwrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_Unwrap.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + destruct ctx.
      eauto.
    + eassumption.

  - (* TermBind *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst. 
    split.
    + apply W_Term.
      * destruct ctx.
        eauto.
      * eapply H.
        -- eassumption.
        -- eassumption.
        -- assumption.
    + reflexivity. 
  - (* TypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split. 
    + apply W_Type.
      destruct ctx.
      eauto.
    + reflexivity.
  - (* DatatypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split.
    + eapply W_Data.
      * reflexivity.
      * intros.
        destruct ctx.
        eapply context_invariance_T__constructor_well_formed.
        eauto.
    + reflexivity.
Qed.

Corollary substitution_preserves_typing__Term : forall t ctx x U v T t',
    extendT x U ctx |-+ t : T ->
    emptyContext |-+ v : U ->
    substitute x v t t' ->
    ctx |-+ t' : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Bindings_NonRec : forall bs ctx x U v bs',
    extendT x U ctx |-oks_nr bs ->
    emptyContext |-+ v : U ->
    substitute_bindings_nonrec x v bs bs' ->
    ctx |-oks_nr bs' /\ List.map binds bs = List.map binds bs'.
Proof.
  intros.
  eapply P_Bindings_NonRec__holds_definitionally; eauto.
  assert (forall bs0, Util.ForallP P_Binding bs0). {
    induction bs0.
    - constructor.
    - constructor.
      + apply substitution_preserves_typing.
      + assumption.
  }
  apply H2.
Qed.

Corollary substitution_preserves_typing__Bindings_Rec : forall bs ctx x U v bs',
    extendT x U ctx |-oks_r bs ->
    emptyContext |-+ v : U ->
    substitute_bindings_rec x v bs bs' ->
    ctx |-oks_r bs' /\ List.map binds bs = List.map binds bs'.
Proof.
  intros.
  eapply P_Bindings_Rec__holds_definitionally; eauto.
  assert (forall bs0, Util.ForallP P_Binding bs0). {
    induction bs0.
    - constructor.
    - constructor.
      + apply substitution_preserves_typing.
      + assumption.
  }
  apply H2.
Qed.