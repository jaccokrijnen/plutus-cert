Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.NormalisationPreservesKinding.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import Coq.Logic.FunctionalExtensionality.

Definition upd (a : tyname) (T' : Ty ) (Gamma : partial_map Ty) :=
  fun x =>
    match Gamma x with
    | None => None
    | Datatypes.Some T => Datatypes.Some (substituteT a T' T)
    end.

Lemma upd_empty : forall X U,
    upd X U empty = empty.
Proof.
  intros X U.
  unfold upd.
  simpl.
  reflexivity.
Qed.

Lemma upd__substituteT : forall Gamma x X U T,
    Gamma x = Datatypes.Some T ->
    (upd X U Gamma) x = Datatypes.Some (substituteT X U T).
Proof.
  intros.
  unfold upd.
  rewrite H.
  reflexivity.
Qed.

Lemma upd_absorbs_substituteT : forall x X U T Gamma,
    (x |-> (substituteT X U T); upd X U Gamma) = upd X U (x |-> T; Gamma).
Proof.
  intros.
  simpl.
  f_equal.
  apply functional_extensionality.
  intros.
  destruct (x =? x0) eqn:Heqb.
  - (* x = x0 *)
    apply eqb_eq in Heqb as Heq.
    subst.
    unfold upd.
    rewrite update_eq.
    rewrite update_eq.
    reflexivity.
  - (* x <> x0 *)
    apply eqb_neq in Heqb as Hneq.
    unfold upd.
    rewrite update_neq; auto.
    rewrite update_neq; auto.
Qed.

(** ** Predicates *)
Definition P_Term (t : Term) :=
  forall Delta Gamma X K U T,
    (X |-> K; Delta) ,, Gamma |-+ t : T ->
    empty |-* U : K ->
    Delta ,, (upd X U Gamma) |-+ <{ [[U / X] t }> : (substituteT X U T).
    
Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma X K U,
    (X |-> K; Delta) ,, Gamma |-ok b ->
    empty |-* U : K ->
    Delta ,, (upd X U Gamma) |-ok <{ [[U / X][b] b }>.

Theorem substituteA_preserves_typing : 
  forall t, P_Term t.
Proof. (*
  apply Term__ind with P_Binding.
  - apply skip.
  - (* Var *)
    intros x. 
    unfold P_Term. 
    intros Delta Gamma X K U T Htyp Hkind.

    inversion Htyp. subst.
    simpl.

    apply T_Var.
    apply upd__substituteT.
    assumption.

    subst.
    simpl.

    apply T_Var.
    apply upd__substituteT.
    apply skip.

  - (* TyAbs*) 
    intros bX K t_body IH__t_body.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    simpl.
    destruct (X =? bX) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      simpl.
      apply skip.
    + apply eqb_neq in Heqb as Hneq.
      apply T_TyAbs.

    inversion Htyp. subst.
    simpl.
    destruct (X =? bX) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      simpl.
      (*
      unfold extendK in H4.
      simpl in H4.
      apply 

      apply T_TyAbs.
      unfold extendK.
      simpl.
      unfold P_Term in IH__t_body.
      eapply IH__t_body.*)
      apply skip.
    + apply eqb_neq in Heqb as Hneq.
      apply T_TyAbs.
      eapply IH__t_body.
      * simpl.
        rewrite update_permute; auto.
        apply H5. 
      * apply Hkind.

    + subst.
    {

    }
  - (* LamAbs *)
    intros bx T0 t_body IH__t_body.
    unfold P_Term. 
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.
    
    simpl.
    apply T_LamAbs.
    + unfold P_Term in IH__t_body.
      rewrite upd_absorbs_substituteT.
      eapply IH__t_body; eauto.
    + simpl.
      eapply substituteT_preserves_kinding.
      * eapply H6.
      * assumption.
  - (* Apply *) 
    intros t1 IH__t1 t2 IH__t2.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.
    
    simpl.

    eapply T_Apply.
    + eapply IH__t1 in H3; eauto.
    + eapply IH__t2; eauto.
  - (* Constant *)
    intros sv.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.

    simpl.
    eauto with typing.
  - (* Builtin *)
    intros d.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.

    destruct d; try simpl; try apply T_Builtin; auto. 
    destruct (X =? "a") eqn:Heqb.
    + reflexivity.
    + reflexivity.
  
  - (* TyInst *)
    intros t_body IH__t_body V.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.
    simpl.

    assert (Delta ,, (upd X U Gamma) |-+ <{ [[U / X] t_body }>: (substituteT X U (Ty_Forall X0 K2 T1))) by eauto.
    
    simpl in H.
    destruct (X =? X0) eqn:Heqb.
    + apply eqb_eq in Heqb. subst.
      eapply T_TyInst.
      * apply H.
      * eapply substituteT_preserves_kinding; eauto.
      * apply skip. (* TODO *)
      * apply skip.
    + eapply T_TyInst.
      * apply H.
      * eapply substituteT_preserves_kinding; eauto.
      * apply skip.
      * apply skip. (* TODO *)
  - (* Error *)
    intros T0.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.

    inversion Htyp. subst.
  
    apply T_Error.
    eapply substituteT_preserves_kinding; eauto.
  - (* IWrap *)
    intros F0 T0 t0 IH__t0.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.
    
    inversion Htyp. subst.
    simpl.

    eapply T_IWrap.
    + apply skip. (* TODO *)
    + eauto.
    + eapply substituteT_preserves_kinding; eauto.
    + eapply substituteT_preserves_kinding; eauto.
  - (* Unwrap *)
    intros t0 IH__t0.
    unfold P_Term.
    intros Delta Gamma X L U T Htyp Hkind.
    
    inversion Htyp. subst.
    simpl.*)
Admitted.