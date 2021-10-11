Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Rules.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import PlutusCert.Util.

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

Definition P_has_type (Delta : Delta) (Gamma : Gamma) (t : Term) (T : Ty) :=
  forall Gamma',
    (forall x, appears_free_in_Term x t -> Gamma x = Gamma' x) ->
    Delta ,, Gamma' |-+ t : T.

Definition P_constructor_well_formed (Delta : Delta) (c : constructor) :=
  Delta |-ok_c c.

Definition P_bindings_well_formed_nonrec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__bindings_nonrec x bs -> Gamma x = Gamma' x) ->
    Delta ,, Gamma' |-oks_nr bs.  

Definition P_bindings_well_formed_rec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__bindings_rec x bs -> Gamma x = Gamma' x) ->
    Delta ,, Gamma' |-oks_r bs.  

Definition P_binding_well_formed (Delta : Delta) (Gamma : Gamma) (b : Binding) :=
  forall Gamma',
    (forall x, appears_free_in_Term__binding x b -> Gamma x = Gamma' x) ->
    Delta ,, Gamma' |-ok b.

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed 
  : core.

Axiom skip : forall P, P.

Theorem context_invariance : 
  (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
  (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
  (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
  (forall Delta Gamma b, Delta ,, Gamma |-ok b -> P_binding_well_formed Delta Gamma b).
Proof with eauto.
  apply has_type__multind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  all: intros; autounfold; intros.
  - (* T_Let *)
    subst.
    eapply T_Let.
    + reflexivity.
    + reflexivity.
    + apply H2.
      intros.
      apply H5.
      apply AFIT_LetNonRec.
      assumption.
    + simpl. apply H4.
      intros.
      apply mupdate_eq_cong.
      apply H5.
      apply AFIT_Let.
      -- apply skip. (* TODO *) 
      -- assumption.
  - (* T_LetRec *)
    subst.
    eapply T_LetRec.
    + reflexivity.
    + reflexivity.
    + apply H2.
      intros.
      apply mupdate_eq_cong.
      apply H5.
      apply AFIT_LetRec; auto.
      apply skip.
    + apply H4.
      intros.
      apply mupdate_eq_cong.
      apply H5.
      apply AFIT_Let.
      -- apply skip. (* TODO *)
      -- assumption.
  - (* T_Var *)
    apply T_Var.
    rewrite <- H0; auto.
  - (* T_TyForall *)
    apply T_TyAbs.
    apply H0.
    intros x Hafi.
    apply H1.
    apply AFIT_TyAbs.
    assumption.
  - (* T_LamAbs *)
    apply T_LamAbs.
    + apply H0.
      intros.
      destruct (x =? x0) eqn:Heqb.
      * apply eqb_eq in Heqb.
        subst.
        rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      * apply eqb_neq in Heqb.
        rewrite update_neq; auto.
        rewrite update_neq; auto.
    + auto.
  - (* T_Apply *)
    apply T_Apply with T1.
    + apply H0.
      intros.
      apply H3.
      apply AFIT_Apply1.
      assumption.
    + apply H2.
      intros.
      apply H3.
      apply AFIT_Apply2.
      assumption.
  - (* T_Constant *)
    apply T_Constant.
  - (* T_Builtin *)
    apply T_Builtin.
    assumption.
  - (* T_TyInst *)
    apply T_TyInst with T1 X K2 T1'.
    + apply H0.
      intros.
      apply H4.
      apply AFIT_TyInst.
      assumption.
    + assumption.
    + assumption.
    + assumption.
  - (* T_Error *)
    apply T_Error.
    assumption.
  - (* T_IWrap *)
    apply T_IWrap with K S.
    + assumption.
    + apply H1.
      intros.
      apply H4.
      apply AFIT_IWrap.
      assumption.
    + assumption.
    + assumption.
  - (* T_Unwrap *)
    apply T_Unwrap with F K T.
    + apply H0.
      intros.
      apply H3.
      apply AFIT_Unwrap.
      assumption.
    + assumption.
    + assumption.
  - (* T_ExtBuiltin *)
    eapply T_ExtBuiltin.
    + eauto.
    + eauto.
    + intros.
      eapply H2.
      all: eauto.
      destruct p.
      simpl.
      intros.
      eapply H4.
      apply AFIT_ExtBuiltin.
      exists t.
      split. apply in_combine_l in H5. assumption.
      auto.
    + auto.
  
  - (* W_Con *)
    econstructor. eauto.
    intros.
    eapply H0.
    assumption.
  
  - (* W_NilB_NonRec *)
    constructor.
  - (* W_ConsB_NonRec *)
    apply W_ConsB_NonRec.
    + apply H0.
      intros.
      apply H3.
      apply AFIT_ConsB1_NonRec.
      assumption.
    + apply H2.
      intros.
      apply mupdate_eq_cong.
      apply H3.
      apply AFIT_ConsB2_NonRec.
      * unfold P_binding_well_formed in H0.
        unfold P_bindings_well_formed_nonrec in H2. apply skip. (* TODO *) 
      * assumption.
  
  - (* W_NilB_Rec *)
    constructor.
  - (* W_ConsB_Rec *)
    apply W_ConsB_Rec.
    + apply H0.
      intros.
      apply H3.
      apply AFIT_ConsB1_Rec.
      assumption.
    + apply H2.
      intros.
      apply H3.
      apply AFIT_ConsB2_Rec.
      assumption.
  
  - (* W_Term *)
    apply W_Term.
    + assumption.
    + apply H1.
      intros.
      apply H2.
      apply AFIT_TermBind.
      assumption.
  - (* W_Type *)
    apply W_Type.
    assumption.
  - (* W_Data *)
    subst.
    eapply W_Data.
    + reflexivity.
    + reflexivity.
    + intros.
      apply H1.
      assumption.
Qed.

    

Lemma free_in_context : forall x t T Delta Gamma,
    appears_free_in_Term x t ->
    Delta ,, Gamma |-+ t : T ->
    exists T', Gamma x = Datatypes.Some T'.
Proof. Admitted.

Corollary typable_empty__closed_Term : forall t T,
    empty ,, empty |-+ t : T ->
    closed_Term t.
Proof.
  intros. unfold closed_Term. intros x H1.
  destruct (free_in_context _ _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.

Corollary typable_emptyT__closed_Term : forall Delta t T,
    Delta ,, empty |-+ t : T ->
    closed_Term t.
Proof.
  intros. unfold closed_Term. intros x H1.
  destruct (free_in_context _ _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.







Lemma free_in_context_Term : forall x t T Delta Gamma,
    appears_free_in_Term x t ->
    Delta ,, Gamma |-+ t : T ->
    exists T', Gamma x = Datatypes.Some T'.
Proof.
  intros x t T Delta Gamma Hafi Htyp.
  generalize dependent x.
  induction Htyp.
  - intros.
    inversion Hafi.
    + subst.
      apply IHHtyp in H7.
      destruct H7.
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
    Delta ,, Gamma |-+ t : T ->
    exists K, Delta X = Datatypes.Some K.
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
    erewrite <- update_neq; eauto.
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
    empty ,, empty |-+ t : T ->
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
