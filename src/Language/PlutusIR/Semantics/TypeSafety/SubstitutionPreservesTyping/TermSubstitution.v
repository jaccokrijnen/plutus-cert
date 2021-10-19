Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.

Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(*
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
    List.In x (bvb a) ->
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
  List.In x (bvbs bs) ->
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
Qed. *)

Definition P_Term (t : Term) :=
  forall Delta Gamma x U v T,
    Delta ,, (x |-> U; Gamma) |-+ t : T ->
    empty ,, empty |-+ v : U ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.

Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma x U v,
    Delta ,, (x |-> U; Gamma) |-ok b ->
    empty ,, empty |-+ v : U ->
    Delta ,, Gamma |-ok <{ [v / x][b] b }> /\ 
    binds_Delta b = binds_Delta <{ [v / x][b] b }> /\
    binds_Gamma b = binds_Gamma <{ [v / x][b] b}>.

#[export] Hint Unfold
  P_Term
  P_Binding
  : core.

Lemma P_letnonrec : forall bs t Delta Gamma x U v T,
    P_Term t ->
    Delta ,, (x |-> U; Gamma) |-+ (Let NonRec bs t) : T ->
    empty ,, empty |-+ v : U ->
    Util.ForallP P_Binding bs ->
    Delta ,, Gamma |-+ <{ [v / x] {Let NonRec bs t} }> : T /\ 
    List.map binds_Delta bs = List.map binds_Delta <{ [v / x][bnr] bs }> /\
    List.map binds_Gamma bs = List.map binds_Gamma <{ [v / x][bnr] bs }>.
Proof.
  induction bs; intros.
  - simpl.
    split.
    + eapply T_Let.
      * reflexivity.
      * simpl; eauto.
      * reflexivity.
      * econstructor.
      * simpl.
        eapply H; eauto.
        inversion H0. subst.
        eauto.
        apply skip.
      
    + auto.
  - inversion H0. subst.
    simpl.
    destruct (List.existsb (eqb x) (bvb a)) eqn:Hexb.
    + (* apply binds_binds_bound_vars in H6 as H15.
      destruct H15 as [U' Hlu].
      split.
      * eapply T_Let.
        -- reflexivity.
        -- apply W_ConsB_NonRec.
           ++ eapply Util.ForallP_hd in H2.
              eapply H2; eauto.
           ++ eapply Util.ForallP_hd in H2.
              unfold P_Binding in H2.
              assert (binds a = binds b') by (eapply H2; eauto).
              rewrite <- H4.
              erewrite append_extendT_shadow in H9; eauto.
        -- eapply weakening; eauto. *)
Admitted.

Lemma P_letrec : forall bs t Delta Gamma x U v T,
    P_Term t ->
    Delta ,, (x |-> U; Gamma) |-+ (Let Rec bs t) : T ->
    empty ,, empty |-+ v : U ->
    Util.ForallP P_Binding bs ->
    Delta ,, Gamma |-+ <{ [v / x] {Let Rec bs t} }> : T /\ 
    List.map binds_Delta bs = List.map binds_Delta <{ [v / x][br] bs }> /\
    List.map binds_Gamma bs = List.map binds_Gamma <{ [v / x][br] bs}>.
Proof. Admitted.

Lemma substitution_preserves_typing : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof.
  apply Term__multind with 
    (P := P_Term) 
    (Q := P_Binding).
  all: intros; autounfold; intros.
  - destruct rec.
    + simpl.
      all: eapply P_letnonrec; eauto.
    + simpl.
      all: eapply P_letrec; eauto.
  - simpl.
    destruct (x =? s) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      inversion H.
      subst.
      rewrite update_eq in H2.
      inversion H2. subst.
      apply has_type__normal in H0 as H7.
      eapply normalisation__stability in H7; eauto.
      subst. 
      eapply weakening_empty; eauto.
    + apply eqb_neq in Heqb as Hneq.
      inversion H. subst.
      eapply T_Var.
      * rewrite update_neq in H2; eauto.
      * eassumption.
  - (* TyAbs *) 
    inversion H0. subst.
    simpl.
    apply T_TyAbs.
    eapply H.
    + eauto.
    + eauto.
  - (* LamAbs *)
    inversion H0. subst.
    simpl.
    destruct (x =? s) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq. 
      subst.
      apply T_LamAbs.
      * assumption.
      * eauto.
      * rewrite update_shadow in H10.
        eauto.
    + apply eqb_neq in Heqb as Hneq.
      apply T_LamAbs.
      * eauto.
      * eauto.
      * eapply H.
      -- rewrite update_permute; auto.
         apply H10.
      -- eassumption.
  - (* Apply *)
    inversion H1. subst.
    simpl.
    eapply T_Apply.
    + eapply H.
      * eassumption.
      * eassumption.
    + eapply H0.
      * eassumption.
      * eassumption.
  - (* Constant *)
    inversion H. subst.
    simpl.
    apply T_Constant.
  - (* Builtin *) 
    inversion H. subst.
    simpl.
    apply T_Builtin.
    reflexivity.
  - (* TyInst *)
    inversion H0. subst.
    simpl.
    eapply T_TyInst.
    + eapply H.
      * eassumption.
      * eassumption.
    + eauto.
    + eassumption.
    + eassumption.
  - (* Error *)
    inversion H. subst.
    simpl.
    apply T_Error.
    eauto.
    eauto.
  - (* IWrap *)
    inversion H0. subst.
    simpl.
    eapply T_IWrap.
    + eassumption.
    + eapply H.
      * eassumption.
      * eassumption.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
  - (* Unwrap *)
    inversion H0. subst.
    simpl.
    eapply T_Unwrap.
    + eapply H.
      * eassumption.
      * eassumption.
    + eauto.
    + eassumption.

  - (* ExtBuiltin *)
    inversion H0. subst.
    simpl.
    erewrite <- List.map_length.
    eapply T_ExtBuiltin; eauto.
    + rewrite List.map_length. auto.
    + intros.
      destruct p.
      simpl.
      apply List.in_combine_l in H2 as H15.
      apply List.in_combine_r in H2 as H16.
      eapply List.in_map_iff in H15 as H17.
      destruct H17. 
      destruct H3.
      subst.

      apply skip.

  - (* TermBind *)
    inversion H0. subst.
    simpl.
    split.
    + apply W_Term.
      * eauto.
      * eapply H.
        -- eassumption.
        -- eassumption.
    + auto. 
  - (* TypeBind *)
    inversion H. subst.
    simpl.
    split. 
    + apply W_Type.
      eauto.
    + auto.
  - (* DatatypeBind *)
    inversion H. subst.
    split.
    + simpl.
      eapply W_Data.
      * reflexivity.
      * reflexivity.
      * intros.
        eauto.
    + auto.
Qed. 

Corollary substitution_preserves_typing__Term : forall t Delta Gamma x U v T,
    Delta ,, (x |-> U; Gamma)  |-+ t : T ->
    empty ,, empty |-+ v : U ->
    Delta ,, Gamma |-+ <{ [v / x] t }> : T.
Proof. apply substitution_preserves_typing. Qed.

Corollary substitution_preserves_typing__Binding : forall b Delta Gamma x U v,
    Delta ,, (x |-> U; Gamma) |-ok b ->
    empty ,, empty |-+ v : U ->
    Delta ,, Gamma |-ok <{ [v / x][b] b }> /\ 
    binds_Delta b = binds_Delta <{ [v / x][b] b }> /\
    binds_Gamma b = binds_Gamma <{ [v / x][b] b }>.
Proof. apply substitution_preserves_typing. Qed.