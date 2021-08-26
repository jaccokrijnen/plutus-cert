Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Weakening.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma append_extendT_shadow : forall ctx' x T U ctx,
    lookupT ctx' x = Datatypes.Some T ->
    Named.append ctx' (x |T-> U; ctx) = Named.append ctx' ctx.
Proof.
  intros.
  unfold Named.append.
  apply cong_eq.
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
  - reflexivity.
Qed.

Lemma append_extendT_permute : forall ctx' x U ctx,
    lookupT ctx' x = None ->
    Named.append ctx' (x |T-> U; ctx) = (x |T-> U; Named.append ctx' ctx).
Proof. 
  intros.
  unfold Named.append.
  apply cong_eq.
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
  - reflexivity.
Qed.


Lemma binds_binds_bound_vars : forall a x U v,
  (exists v, List.In v (term_vars_bound_by_binding a) -> x = v) ->
  emptyContext |-+ v : U ->
  lookupT (binds a) x = Datatypes.Some U.
Proof. Admitted.

Lemma binds_unbinds_unbound_vars : forall a x,
  ~(exists v, List.In v (term_vars_bound_by_binding a) -> x = v) ->
  lookupT (binds a) x = None.
Proof. Admitted.

Theorem context_invariance_T__has_kind : forall T ctx_T ctx_K K ctx_T',
  (ctx_T, ctx_K) |-* T : K ->
  (ctx_T', ctx_K) |-* T : K.
Proof.
  induction T.
  - intros.
    inversion H. subst.
    apply K_Var.
    assumption.
  - intros.
    inversion H. subst.
    apply K_Fun. 
    + eapply IHT1. eauto.
    + eapply IHT2. eauto.
  - intros.
    inversion H. subst.
    eapply K_IFix.
    + eapply IHT2. eauto.
    + eapply IHT1. eauto.
  - intros. 
    inversion H. subst.
    apply K_Forall.
    eapply IHT. eauto.
  - intros.
    inversion H. subst.
    apply K_Builtin.
  - intros.
    inversion H. subst.
    eapply K_Lam.
    eapply IHT.
    eauto.
  - intros.
    inversion H. subst.
    eapply K_App.
    + eapply IHT1. eauto.
    + eapply IHT2. eauto.
Qed.

Lemma context_invariance_T__constructor_well_formed : forall ctx_T' ctx_T ctx_K c ,
  (ctx_T, ctx_K) |-ok_c c ->
  (ctx_T', ctx_K) |-ok_c c.
Proof.
  intros.
  inversion H. subst.
  apply W_Con.
  intros.
  eapply context_invariance_T__has_kind.
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

Definition P_Binding (b : Binding) :=
  forall ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
#[export] Hint Unfold P_Binding : core.

Definition P_Bindings_NonRec (bs : list Binding) :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_nr bs ->
    emptyContext |-+ v : U ->
    Util.ForallT P_Binding bs ->
    substitute_bindings_nonrec x v bs bs' ->
    ctx |-oks_nr bs' /\ List.map binds bs = List.map binds bs'.

Lemma e : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H1. subst.
    auto with typing.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H1.
    + subst.
      split.
      * apply W_ConsB_NonRec.
        -- apply Util.ForallT_hd in X.
          unfold P_Binding in X.
          eapply X.
          ++ inversion H. subst.
             apply H5.
          ++ apply H0.
          ++ assumption.
        -- apply Util.ForallT_hd in X.
           unfold P_Binding in X.
           inversion H. subst.
           destruct (X _ _ _ _ _ H5 H0 H8).
           rewrite <- H3.
           erewrite append_extendT_shadow in H7; eauto.
           eapply binds_binds_bound_vars; eauto.
      * simpl.
        apply Util.ForallT_hd in X.
        inversion H. subst.
        assert (binds a = binds b'). {
          eapply X; eauto.
        }
        subst.
        f_equal; auto.
    + subst.
      split.
      * apply W_ConsB_NonRec.
        -- apply Util.ForallT_hd in X.
           apply X with x U v.
           ++ inversion H. subst.
              assumption.
           ++ assumption.
           ++ assumption.
        -- apply Util.ForallT_hd in X as X0.
           unfold P_Binding in X0.
           inversion H. subst.
           destruct (X0 _ _ _ _ _ H6 H0 H7).
           rewrite <- H3.
           eapply IHbs.
           ++ rewrite append_extendT_permute in H8; eauto.
              apply binds_unbinds_unbound_vars; auto.
           ++ apply H0.
           ++ apply Util.ForallT_tl in X. assumption.
           ++ apply H9.
      * simpl.
        apply Util.ForallT_hd in X as X0.
        inversion H. subst.
        assert (binds a = binds b'). {
          eapply X0; eauto.
        }
        f_equal; auto.
        eapply IHbs; eauto.
        -- rewrite append_extendT_permute in H8; eauto.
           apply binds_unbinds_unbound_vars; eauto.
        -- eapply Util.ForallT_tl. eauto.
Qed.

Axiom skip : forall P, P.

Lemma substitution_preserves_typing : forall t, P_Term t.
Proof.
  apply Term_rect' with (P := P_Term) (Q := P_Binding).
  - intros. autounfold. intros.
    inversion H2.
    + subst.
      eapply T_Let.
      * reflexivity.
      * eapply e.
        -- inversion H0. subst.
            eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * inversion H0. subst.
        apply skip.
    + subst.
      inversion H0. subst.
      eapply T_Let.
      * reflexivity.
      * eapply e.
        -- inversion H0. subst.
           eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * apply skip.
    + apply skip.
    + apply skip.
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
        eapply context_invariance_T__has_kind.
        eauto.
    + subst.
      apply T_LamAbs.
      * eapply H.
        -- rewrite extendT_permute in H8; auto.
           apply H8.
        -- eassumption.
        -- assumption.
      * destruct ctx.
        eapply context_invariance_T__has_kind.
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
      eapply context_invariance_T__has_kind.
      eauto.
    + assumption.
  - (* Error *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Error.
    destruct ctx.
    eapply context_invariance_T__has_kind.
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
      eapply context_invariance_T__has_kind.
      eauto.
    + destruct ctx.
      eapply context_invariance_T__has_kind.
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
      eapply context_invariance_T__has_kind.
      eauto.
    + eassumption.

  - (* TermBind *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst. 
    split.
    + apply W_Term.
      * destruct ctx.
        eapply context_invariance_T__has_kind.
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
      eapply context_invariance_T__has_kind.
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
