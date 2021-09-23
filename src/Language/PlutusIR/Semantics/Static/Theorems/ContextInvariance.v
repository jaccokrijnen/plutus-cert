Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Rules.

Require Import Coq.Lists.List.

(** * Context invariance *)

(** ** Type-level context invariance *)


  


(** *** Context invariance (Lemma) *)
Lemma context_invariance__typelevel : forall Delta Delta' T K,
    Delta |-* T : K ->
    (forall X, appears_free_in_Ty X T -> Delta X = Delta' X) ->
    Delta' |-* T : K.
Proof with auto.
  intros Delta Delta' T K HK.
  generalize dependent Delta'.
  induction HK; intros; try solve [econstructor; auto].
  - apply K_Var.
    rewrite <- H0...
  - (* K_Forall *)
    apply K_Forall.
    apply IHHK.
    intros.
    destruct (X =? X0) eqn:Heqb.
    + apply eqb_eq in Heqb.
      subst.
      rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + apply eqb_neq in Heqb.
      rewrite update_neq...
      rewrite update_neq...
  - (* K_Lam *)
    apply K_Lam.
    apply IHHK.
    intros.
    destruct (X =? X0) eqn:Heqb.
    + apply eqb_eq in Heqb.
      subst.
      rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + apply eqb_neq in Heqb.
      rewrite update_neq...
      rewrite update_neq...
Qed.

(** *** Free variables are in context (Lemma) *)

Lemma free_in_context__Ty : forall X T K Delta,
    appears_free_in_Ty X T ->
    Delta |-* T : K ->
    exists K', Delta X = Datatypes.Some K'.
Proof with eauto.
  intros X T K Delta Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - rewrite update_neq in IHHtyp; auto.
  - rewrite update_neq in IHHtyp; auto.
Qed.

Corollary typable_empty__closed_Ty : forall T K,
    empty |-* T : K ->
    closed_Ty T.
Proof.
  intros. unfold closed_Ty. intros x H1.
  destruct (free_in_context__Ty _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

(** ** Term-level context invariance *)



(** ** Context invariance (Theorem) *)

Definition P_has_type (Gamma : Context) (t : Term) (T : Ty) :=
  forall Gamma',
    (forall x, appears_free_in_Term x t -> lookupT Gamma x = lookupT Gamma' x) ->
    (forall X, lookupK Gamma X = lookupK Gamma' X) ->
    Gamma' |-+ t : T.

Definition P_constructor_well_formed (Gamma : Context) (c : constructor) :=
  forall Gamma',
    (forall X, lookupK Gamma X = lookupK Gamma' X) ->
    Gamma' |-ok_c c.

Definition P_bindings_well_formed_nonrec (Gamma : Context) (bs : list Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__bindings_nonrec x bs -> lookupT Gamma x = lookupT Gamma' x) ->
    (forall X, lookupK Gamma X = lookupK Gamma' X) ->
    Gamma' |-oks_nr bs.  

Definition P_bindings_well_formed_rec (Gamma : Context) (bs : list Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__bindings_rec x bs -> lookupT Gamma x = lookupT Gamma' x) ->
    (forall X, lookupK Gamma X = lookupK Gamma' X) ->
    Gamma' |-oks_r bs.  

Definition P_binding_well_formed (Gamma : Context) (b : Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__binding x b -> lookupT Gamma x = lookupT Gamma' x) ->
    (forall X, lookupK Gamma X = lookupK Gamma' X) ->
    Gamma' |-ok b.

Axiom skip : forall P, P.

Theorem context_invariance : 
  (forall Gamma t T, Gamma |-+ t : T -> P_has_type Gamma t T) /\
  (forall Gamma bs, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Gamma bs) /\
  (forall Gamma bs, Gamma |-oks_r bs -> P_bindings_well_formed_rec Gamma bs) /\
  (forall Gamma b, Gamma |-ok b -> P_binding_well_formed Gamma b).
Proof with eauto.
  apply has_type__multind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  - (* T_Let *)
    intros. unfold P_has_type. intros.
    subst.
    eapply T_Let.
    + reflexivity.
    + apply H1.
      * intros.
        apply H4.
        apply AFIT_LetNonRec.
        assumption.
      * assumption.
    + apply H3.
      * intros.
        apply lookupT_append_r.
        apply H4.
        apply AFIT_Let.
        -- apply skip. (* TODO *) 
        -- assumption.
      * intros.
        apply lookupK_append_r.
        apply H5.
  - (* T_LetRec *)
    intros. unfold P_has_type. intros.
    subst.
    eapply T_LetRec.
    + reflexivity.
    + apply H1.
      * intros.
        apply lookupT_append_r.
        apply H4.
        apply AFIT_LetRec; auto.
        apply skip. (* TODO *)
      * intros.
        apply lookupK_append_r.
        apply H5.
    + apply H3.
      * intros.
        apply lookupT_append_r.
        apply H4.
        apply AFIT_Let.
        -- apply skip. (* TODO *)
        -- assumption.
      * intros.
        apply lookupK_append_r.
        apply H5.
  - (* T_Var *)
    intros. unfold P_has_type. intros.
    apply T_Var.
    rewrite <- H0; auto.
  - (* T_TyForall *)
    intros. unfold P_has_type. intros.
    apply T_TyAbs.
    apply H0.
    + intros x Hafi.
      rewrite lookupT_extendK.
      rewrite lookupT_extendK.
      apply H1.
      apply AFIT_TyAbs.
      assumption.
    + intros Y.
      destruct (X =? Y) eqn:Heqb.
      * apply eqb_eq in Heqb.
        subst.
        rewrite lookupK_eq.
        rewrite lookupK_eq.
        reflexivity.
      * apply eqb_neq in Heqb.
        rewrite lookupK_neq; auto.
        rewrite lookupK_neq; auto.
  - (* T_LamAbs *)
    intros. unfold P_has_type. intros.
    apply T_LamAbs.
    + apply H0.
      * intros.
        destruct (x =? x0) eqn:Heqb.
        -- apply eqb_eq in Heqb.
          subst.
          rewrite lookupT_eq.
          rewrite lookupT_eq.
          reflexivity.
        -- apply eqb_neq in Heqb.
          rewrite lookupT_neq; auto.
          rewrite lookupT_neq; auto.
      * intros.
        -- rewrite lookupK_extendT.
           rewrite lookupK_extendT.
           apply H3.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H3.
  - (* T_Apply *)
    intros. unfold P_has_type. intros.
    apply T_Apply with T1.
    + apply H0.
      * intros.
        apply H3.
        apply AFIT_Apply1.
        assumption.
      * intros.
        apply H4.
    + apply H2.
      * intros.
        apply H3.
        apply AFIT_Apply2.
        assumption.
      * intros.
        apply H4.
  - (* T_Constant *)
    intros. unfold P_has_type. intros.
    apply T_Constant.
  - (* T_Builtin *)
    intros. unfold P_has_type. intros.
    apply T_Builtin.
  - (* T_TyInst *)
    intros. unfold P_has_type. intros.
    apply T_TyInst with T1 X K2.
    + apply H0.
      * intros.
        apply H3.
        apply AFIT_TyInst.
        assumption.
      * intros.
        apply H4.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H4.
    + assumption.
  - (* T_Error *)
    intros. unfold P_has_type. intros.
    apply T_Error.
    apply context_invariance__typelevel with (fst ctx).
    + assumption.
    + intros.
      apply H1.
  - (* T_IWrap *)
    intros. unfold P_has_type. intros.
    apply T_IWrap with K S.
    + assumption.
    + apply H1.
      * intros.
        apply H4.
        apply AFIT_IWrap.
        assumption.
      * intros.
        apply H5.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H5.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H5.
  - (* T_Unwrap *)
    intros. unfold P_has_type. intros.
    apply T_Unwrap with F K T.
    + apply H0.
      * intros.
        apply H3.
        apply AFIT_Unwrap.
        assumption.
      * intros.
        apply H4.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H4.
    + assumption.
  
  - (* W_Con *)
    intros. unfold P_constructor_well_formed. intros.
    constructor.
    intros.
    destruct Gamma'.
    destruct ctx.
    eapply context_invariance__typelevel.
    + apply H.
      assumption.
    + intros.
      apply H0.
  
  - (* W_NilB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    constructor.
  - (* W_ConsB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    apply W_ConsB_NonRec.
    + apply H0.
      intros.
      apply H3.
      apply AFIT_ConsB1_NonRec.
      * assumption.
      * assumption.
    + apply H2.
      intros.
      apply lookupT_append_r.
      apply H3.
      apply AFIT_ConsB2_NonRec.
      * unfold P_binding_well_formed in H0.
        unfold P_bindings_well_formed_nonrec in H2. apply skip. (* TODO *) 
      * assumption.
      * intros.
        apply lookupK_append_r.
        apply H4.
  
  - (* W_NilB_Rec *)
    intros. unfold P_bindings_well_formed_rec. intros.
    constructor.
  - (* W_ConsB_Rec *)
    intros. unfold P_bindings_well_formed_rec. intros.
    apply W_ConsB_Rec.
    + apply H0.
      * intros.
        apply H3.
        apply AFIT_ConsB1_Rec.
        assumption.
      * assumption.
    + apply H2.
      * intros.
        apply H3.
        apply AFIT_ConsB2_Rec.
        assumption.
      * assumption.
  
  - (* W_Term *)
    intros. unfold P_binding_well_formed. intros.
    apply W_Term.
    + apply context_invariance__typelevel with (fst ctx).
      * assumption.
      * intros.
        apply H3.
    + apply H1.
      * intros.
        apply H2.
        apply AFIT_TermBind.
        assumption.
      * intros.
        apply H3.
  - (* W_Type *)
    intros. unfold P_binding_well_formed. intros.
    apply W_Type.
    apply context_invariance__typelevel with (fst ctx).
    * assumption.
    * intros.
      apply H1.
  - (* W_Data *)
    intros. unfold P_binding_well_formed. intros.
    subst.
    eapply W_Data.
    + reflexivity.
    + intros.
      apply H1.
      * assumption. 
      * intros.
        apply lookupK_append_r.
        apply H3.
Qed.

    

Lemma free_in_context : forall x t T Gamma,
    appears_free_in_Term x t ->
    Gamma |-+ t : T ->
    exists T', lookupT Gamma x = Datatypes.Some T'.
Proof. Admitted.

Corollary typable_empty__closed_Term : forall t T,
    emptyContext |-+ t : T ->
    closed_Term t.
Proof.
  intros. unfold closed_Term. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Corollary typable_emptyT__closed_Term : forall ctxK t T,
    (ctxK, empty) |-+ t : T ->
    closed_Term t.
Proof.
  intros. unfold closed_Term. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.







Lemma free_in_context_Term : forall x t T Delta Gamma,
    appears_free_in_Term x t ->
    (Delta, Gamma) |-+ t : T ->
    exists T', lookupT (Delta, Gamma) x = Datatypes.Some T'.
Proof.
  intros x t T Delta Gamma Hafi Htyp.
  generalize dependent x.
  induction Htyp.
  - intros.
    inversion Hafi.
    + subst.
      apply IHHtyp in H6.
      destruct H6.
      apply skip.
    + subst.
      apply skip.
  - apply skip.
  - (* T_Var *)
    intros.
    inversion Hafi.
    subst.
    exists T. 
    assumption.
  - (* T_TyAbs *)
    intros.
    inversion Hafi.
    subst.
    simpl in IHHtyp.
    apply IHHtyp.
    assumption.
Admitted.

Lemma free_in_context_Annotation : forall X t T Delta Gamma,
    appears_free_in_Annotation X t ->
    (Delta, Gamma) |-+ t : T ->
    exists K, lookupK (Delta, Gamma) X = Datatypes.Some K.
Proof.
  intros x t T Delta Gamma Hafi Htyp.
  generalize dependent x.
  induction Htyp.
  - apply skip.
  - apply skip.
  - intros.
    inversion Hafi. 
  - intros.
    inversion Hafi.
    subst.
    erewrite <- lookupK_neq; eauto.
  - intros.
    inversion Hafi.
    + subst.
      eapply free_in_context__Ty; eauto.
    + subst.
      simpl in IHHtyp.
      apply IHHtyp.
      assumption.
  - intros. 
    inversion Hafi. 
    + subst.
      apply IHHtyp1.
      assumption.
    + subst.
      apply IHHtyp2.
      assumption.
Admitted.

Corollary typable_empty__closed : forall t T,
    emptyContext |-+ t : T ->
    closed t.
Proof.
  intros. unfold closed.
  split.
  - intros x H1.
    destruct (free_in_context_Term _ _ _ _ _ H1 H) as [T' C].
    discriminate C.
  - intros X H1.
    destruct (free_in_context_Annotation _ _ _ _ _ H1 H) as [K C].
    discriminate C.
Qed.
