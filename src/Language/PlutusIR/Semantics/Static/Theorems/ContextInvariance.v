Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Typing.

Local Open Scope string_scope.

Module Kinding.

  Lemma context_invariance : forall Delta Delta' T K,
      Delta |-* T : K ->
      (forall X, Ty.appears_free_in X T -> Delta X = Delta' X) ->
      Delta' |-* T : K.
  Proof with auto.
    intros Delta Delta' T K HK.
    generalize dependent Delta'.
    induction HK; intros; try solve [econstructor; eauto].
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

End Kinding.

Module Typing.

  Definition P_has_type (Delta : Delta) (Gamma : Gamma) (t : Term) (T : Ty) :=
    forall Gamma',
      (forall x, Term.appears_free_in x t -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-+ t : T.

  Definition P_constructor_well_formed (Delta : Delta) (c : constructor) (T : Ty) :=
    Delta |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__bindings_nonrec x bs -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-oks_nr bs.  

  Definition P_bindings_well_formed_rec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__bindings_rec x bs -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-oks_r bs.  

  Definition P_binding_well_formed (Delta : Delta) (Gamma : Gamma) (b : Binding) :=
    forall Gamma',
      (forall x, Term.appears_free_in__binding x b -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-ok_b b.

  #[export] Hint Unfold 
    P_has_type
    P_constructor_well_formed
    P_bindings_well_formed_nonrec
    P_bindings_well_formed_rec
    P_binding_well_formed 
    : core.

  Theorem context_invariance : 
    (forall Delta Gamma t T, Delta ,, Gamma |-+ t : T -> P_has_type Delta Gamma t T) /\
    (forall Delta Gamma bs, Delta ,, Gamma |-oks_nr bs -> P_bindings_well_formed_nonrec Delta Gamma bs) /\
    (forall Delta Gamma bs, Delta ,, Gamma |-oks_r bs -> P_bindings_well_formed_rec Delta Gamma bs) /\
    (forall Delta Gamma b, Delta ,, Gamma |-ok_b b -> P_binding_well_formed Delta Gamma b).
  Proof with eauto.
    apply has_type__multind with
      (P := P_has_type)
      (P0 := P_constructor_well_formed)
      (P1 := P_bindings_well_formed_nonrec)
      (P2 := P_bindings_well_formed_rec)
      (P3 := P_binding_well_formed).
    all: intros; autounfold; intros.
    all: try solve [econstructor; eauto].

    - (* T_Var *)
      eapply T_Var...
      rewrite <- H1; auto.
    - (* T_LamAbs *)
      apply T_LamAbs...
      apply H2.
      intros.
      destruct (x =? x0) eqn:Heqb.
      + apply eqb_eq in Heqb.
        subst.
        rewrite update_eq.
        rewrite update_eq.
        reflexivity.
      + apply eqb_neq in Heqb.
        rewrite update_neq; auto.
        rewrite update_neq; auto.
    - (* T_Let *)
      subst.
      eapply T_Let...
      simpl. apply H5.
      intros.
      apply mupdate_eq_cong.
      apply H7.
      apply Term.AFIT_Let...
      admit.

    - (* T_LetRec *)
      subst.
      eapply T_LetRec...
      + apply H3.
        intros.
        apply mupdate_eq_cong.
        apply H7.
        apply Term.AFIT_LetRec...
        admit.
      + apply H5.
        intros.
        apply mupdate_eq_cong.
        apply H7.
        apply Term.AFIT_Let...
        admit.
  Admitted.

End Typing.