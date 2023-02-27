Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.In_Auxiliary.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Typing.
Require Import PlutusCert.Util.In.

Require Import Coq.Lists.List.

Local Open Scope string_scope.



Module Kinding.

  Lemma context_invariance : forall Delta Delta' T K,
      Delta |-* T : K ->
      (forall X, appears_free_in_ty X T -> Delta X = Delta' X) ->
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
      (forall x, appears_free_in_tm x t -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-+ t : T.

  Definition P_constructor_well_formed (Delta : Delta) (c : constructor) (T : Ty) :=
    Delta |-ok_c c : T.

  Definition P_bindings_well_formed_nonrec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall Gamma',
      (forall x, appears_free_in_tm__bindings_nonrec x bs -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-oks_nr bs.  

  Definition P_bindings_well_formed_rec (Delta : Delta) (Gamma : Gamma) (bs : list Binding) :=
    forall Gamma',
      (forall x, appears_free_in_tm__bindings_rec x bs -> Gamma x = Gamma' x) ->
      Delta ,, Gamma' |-oks_r bs.  

  Definition P_binding_well_formed (Delta : Delta) (Gamma : Gamma) (b : Binding) :=
    forall Gamma',
      (forall x, appears_free_in_tm__binding x b -> Gamma x = Gamma' x) ->
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
      apply H5.
      intros.
      assert ({In x (BoundVars.bvbs bs)} + {~ In x (BoundVars.bvbs bs)}) by eauto using in_dec, string_dec.
      destruct H1.
      + apply In_bvbs_bindsG in i.
        eapply In__map_normalise in i...
        apply In__lookup_mupdate...
      + apply NameIn_In_neq in n.
        apply mupdate_eq_cong...
    - (* T_LetRec *)
      subst.
      eapply T_LetRec...
      + apply H3.
        intros.
        assert ({In x (BoundVars.bvbs bs)} + {~ In x (BoundVars.bvbs bs)}) by eauto using in_dec, string_dec.
        destruct H1.
        * apply In_bvbs_bindsG in i.
          eapply In__map_normalise in i...
          apply In__lookup_mupdate...
        * apply NameIn_In_neq in n.
          apply mupdate_eq_cong...
      + apply H5.
        intros.
        assert ({In x (BoundVars.bvbs bs)} + {~ In x (BoundVars.bvbs bs)}) by eauto using in_dec, string_dec.
        destruct H1.
        * apply In_bvbs_bindsG in i.
          eapply In__map_normalise in i...
          apply In__lookup_mupdate...
        * apply NameIn_In_neq in n.
          apply mupdate_eq_cong...
    - (* W_ConsB_NonRec *)
      eapply W_ConsB_NonRec...
      eapply H3.
      intros.
      assert ({In x (BoundVars.bvb b)} + {~ In x (BoundVars.bvb b)}) by eauto using in_dec, string_dec.
      destruct H6.
      + apply In_bvb_bindsG in i.
        eapply In__map_normalise in i...
        apply In__lookup_mupdate...
      + apply NameIn_In_neq in n.
        apply mupdate_eq_cong...
  Qed.

End Typing.
