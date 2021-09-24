Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
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

Lemma upd_absorbs_substituteT : forall x X U T Delta Gamma,
    x |T-> (substituteT X U T); (Delta, upd X U Gamma) = (Delta, upd X U (x |-> T; Gamma)).
Proof.
  intros.
  unfold extendT.
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
  -  (* x <> x0 *)
    apply eqb_neq in Heqb as Hneq.
    unfold upd.
    rewrite update_neq; auto.
    rewrite update_neq; auto.
Qed.


(** ** Predicates *)
Definition P_Term (t : Term) :=
  forall Delta Gamma X K U T t',
    (X |K-> K; (Delta, Gamma)) |-+ t : T ->
    empty |-* U : K ->
    substituteA X U t t' ->
    (Delta, upd X U Gamma) |-+ t' : (substituteT X U T).
    
Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma X K U b',
    (X |K-> K; (Delta, Gamma)) |-ok b ->
    empty |-* U : K ->
    substituteA_binding X U b b' ->
    (Delta, upd X U Gamma) |-ok b'.


Theorem substituteA_preserves_typing : 
  forall t, P_Term t.
Proof.
  apply Term__ind with P_Binding.
  - apply skip.
  - (* Var *)
    intros x. 
    unfold P_Term. 
    intros Delta Gamma X K U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    apply T_Var.
    simpl in H1.
    simpl.
    apply upd__substituteT.
    assumption.
  - (* TyAbs*) 
    intros bX K t_body IH__t_body.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'.
    + subst.
      simpl.
      rewrite eqb_refl.
      apply T_TyAbs.
      unfold extendK.
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
    + subst.
      simpl.
      apply eqb_neq in H6 as Heqb.
      rewrite Heqb.
      apply T_TyAbs.
      eapply IH__t_body.
      * simpl.
        rewrite extendK_permute in H4.
        apply H4. 
        assumption.
      * apply Hkind.
      * assumption.
  - (* LamAbs *)
    intros bx T0 t_body IH__t_body.
    unfold P_Term. 
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.
    
    simpl.
    apply T_LamAbs.
    + unfold P_Term in IH__t_body.
      rewrite upd_absorbs_substituteT.
      eapply IH__t_body; eauto.
      unfold extendT in H4.
      simpl in H4.
      apply H4.
    + simpl. 
      eapply substituteT_preserves_kinding.
      * eapply H5.
      * assumption.
  - (* Apply *) 
    intros t1 IH__t1 t2 IH__t2.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    eapply T_Apply.
    + eapply IH__t1 in H2; eauto.
    + eapply IH__t2; eauto.
  - (* Constant *)
    intros sv.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    eauto with typing.
  - (* Builtin *)
    intros d.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    destruct d; try simpl; try apply T_Builtin. 
    destruct (X =? "a") eqn:Heqb.
    + apply T_Builtin.
    + apply T_Builtin.
  
  - (* TyInst *)
    intros t_body IH__t_body V.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    assert ((Delta, upd X U Gamma) |-+ t0' : (substituteT X U (Ty_Forall X0 K2 T1))) by eauto.
    
    simpl in H.
    destruct (X =? X0) eqn:Heqb.
    + eapply T_TyInst.
      * apply H.
      * eapply substituteT_preserves_kinding; eauto.
        simpl in H3.
        apply H3.
      * apply skip. (* TODO *)
    + eapply T_TyInst.
      * apply H.
      * eapply substituteT_preserves_kinding; eauto.
        simpl in H3.
        apply H3.
      * apply skip. (* TODO *)
  - (* Error *)
    intros T0.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    apply T_Error.
    eapply substituteT_preserves_kinding; eauto.
    apply H1.
  - (* IWrap *)
    intros F0 T0 t0 IH__t0.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.
    
    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    simpl.
    eapply T_IWrap.
    + eauto.
    + apply skip. (* TODO *) 
    + eapply substituteT_preserves_kinding; eauto.
      apply H6.
    + eapply substituteT_preserves_kinding; eauto.
      apply H7.
  - (* Unwrap *)
    intros t0 IH__t0.
    unfold P_Term.
    intros Delta Gamma X L U T t' Htyp Hkind Hsa__t'.
    
    inversion Htyp. subst.
    inversion Hsa__t'. subst.

Admitted.