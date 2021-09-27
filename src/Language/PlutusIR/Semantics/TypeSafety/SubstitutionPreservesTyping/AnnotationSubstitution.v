Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.TypeSubstitution.

Require Import Coq.Logic.FunctionalExtensionality.

Definition tass := list (name * Ty).

Fixpoint mupdate {X:Type} (m : partial_map X) (xts : list (string * X)) :=
  match xts with
  | nil => m
  | ((x, v) :: xts') => x |-> v ; (mupdate m xts')
  end.
  
Fixpoint lookup {X:Type} (k : string) (l : list (name * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if String.eqb j k then Datatypes.Some x else lookup k l'
  end.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if String.eqb n' n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Inductive UpdateContext (X : tyname) (U : Ty) : tass -> tass -> Prop :=
  | UC_nil :
      UpdateContext X U nil nil
  | UC_Some : forall x T T' c c',
      UpdateContext X U c c' ->
      substituteTCA X U T T' ->
      UpdateContext X U ((x, T) :: c) ((x, T') :: c').

Lemma UpdateContext_domains_match : forall X U c c',
    UpdateContext X U c c' ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      exists T',
        lookup x c' = Datatypes.Some T'.
Proof.
  intros X U c c' UC.
  induction UC; intros x0 T0 C.
  - discriminate.
  - simpl. 
    simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + exists T'. auto.
    + apply IHUC with T0.
      auto.
Qed.

Lemma UpdateContext_substituteTCA : forall X U c c',
    UpdateContext X U c c' ->
    forall x T T',
      lookup x c = Datatypes.Some T ->
      lookup x c' = Datatypes.Some T' ->
      substituteTCA X U T T'.
Proof.
  intros X U c c' UC.
  induction UC; intros x' T0' T0'' E1 E2.
  - destruct x'; discriminate.
  - inversion E1. subst.
    inversion E2. subst.
    destruct (x =? x').
    + inversion H1. subst.
      inversion H2. subst.
      assumption. 
    + apply IHUC with x'; assumption.
Qed.

Lemma mupdate_lookup : forall (c : tass) (x : name),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    destruct a.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_eq.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_neq; auto.
Qed.

(** ** Predicates *)
Definition P_Term (t : Term) :=
  forall Delta Gamma Gamma' X U c c', 
    UpdateContext X U c c' ->
    Gamma = mupdate empty c ->
    Gamma' = mupdate empty c' -> 
    forall K t' T T',
      (X |K-> K; (Delta, Gamma)) |-+ t : T ->
      empty |-* U : K ->
      substituteA X U t t' ->
      substituteTCA X U T T' ->
      (Delta, Gamma') |-+ t' : T'.
    
Definition P_Binding (b : Binding) : Prop :=
  forall Delta Gamma Gamma' X U c c',
    UpdateContext X U c c' ->
    Gamma = mupdate empty c ->
    Gamma' = mupdate empty c' ->
    forall K b',
      (X |K-> K; (Delta, Gamma)) |-ok b ->
      empty |-* U : K ->
      substituteA_binding X U b b' ->
      (Delta, Gamma') |-ok b'.


Theorem substituteA_preserves_typing : 
  forall t, P_Term t.
Proof.
  apply Term__ind with P_Binding.
  (*- apply skip.
  - (* Var *)
    intros x. 
    unfold P_Term. 
    intros Delta Gamma X K U T t' c c' Gamma' T'. 
    intros UC Heq Heq' Htyp Hkind Hsa__t' Hstca__T'.

    assert (forall x, (mupdate empty c) x = lookup x c). {
      intros. erewrite mupdate_lookup. auto.
    }

    inversion Htyp. subst.
    inversion Hsa__t'. subst.

    simpl in H2.
    rewrite H in H2.

    destruct (UpdateContext_domains_match _ _ _ _ UC _ _ H2) as [T0' Hlu__T'].

    apply T_Var.
    + simpl. rewrite <- mupdate_lookup. assumption. apply Hlu__T'. apply UpdateContext_substituteTCA.

    eapply UpdateContext_domains_match in UC.
    + apply T_Var.
      simpl.
        simpl in H2.
        apply UC.
      apply H2.

    apply T_Var.
    simpl in H1.
    simpl.
    apply skip.
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

    assert ((Delta, UpdateContext X U Gamma) |-+ t0' : (substituteT X U (Ty_Forall X0 K2 T1))) by eauto.
    
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
    inversion Hsa__t'. subst.*)

Admitted.