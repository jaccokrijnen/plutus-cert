Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Import PlutusCert.Util.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.

Definition P_Term (t : Term) : Prop :=
  forall x s,
    exists t', substitute x s t t'.

Definition P_Binding (b : Binding) : Prop :=
  forall x s,
    exists b', substitute_binding x s b b'.

Definition P_Bindings_NonRec (bs : list Binding) : Prop :=
  forall x s,
    ForallP P_Binding bs ->
    exists bs', substitute_bindings_nonrec x s bs bs'.

Definition P_Bindings_Rec (bs : list Binding) : Prop :=
  forall x s,
    ForallP P_Binding bs ->
    exists bs', substitute_bindings_rec x s bs bs'.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec. intros.
    exists nil.
    apply S_NilB_NonRec.
  - rename a into b. 
    unfold P_Bindings_NonRec. intros.
    apply ForallP_uncons in H.
    destruct H.
    destruct p with x s.
    rename x0 into b'.
    assert (exists bs', substitute_bindings_nonrec x s bs bs') by eauto.
    destruct H0 as [bs' H0].

    assert ({In x (term_vars_bound_by_binding b)} + {~ In x (term_vars_bound_by_binding b)}) by eauto using in_dec, string_dec.
    destruct H1.
    + exists (b' :: bs).
      apply S_ConsB_NonRec1; auto.
    + exists (b' :: bs').
      apply S_ConsB_NonRec2; auto.
Qed. 


Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec. intros.
    exists nil.
    apply S_NilB_Rec.
  - rename a into b. 
    unfold P_Bindings_Rec. intros.
    apply ForallP_uncons in H.
    destruct H.
    destruct p with x s.
    rename x0 into b'.
    assert (exists bs', substitute_bindings_rec x s bs bs') by eauto.
    destruct H0 as [bs' H0].

    exists (b' :: bs').
    apply S_ConsB_Rec; auto.
Qed.

Lemma substitute_models_total_function : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  - (* Let *)
    intros rec bs t FPbs IHt. 
    unfold P_Term. 
    intros x s.

    assert (temp: exists bs', substitute_bindings_nonrec x s bs bs') by (eapply P_Bindings_NonRec__holds_definitionally; eauto).
    destruct temp as [bs'_nr Hsubst_nr].
    assert (temp: exists bs', substitute_bindings_rec x s bs bs') by (eapply P_Bindings_Rec__holds_definitionally; eauto).
    destruct temp as [bs'_r Hsubst_r].
    assert (temp: exists t', substitute x s t t') by eauto.
    destruct temp as [t' Hsubst].

    assert ({In x (term_vars_bound_by_bindings bs)} + {~ In x (term_vars_bound_by_bindings bs)}) 
      by eauto using in_dec, string_dec.

    all: destruct rec.
    all: destruct H.
    + eexists. apply S_Let1. assumption. eassumption. 
    + eexists. apply S_Let2. assumption. eassumption. eassumption. 
    + eexists. apply S_LetRec1. assumption. 
    + eexists. apply S_LetRec2. assumption. eassumption. eassumption.

  - (* Var *)
    intros y. 
    unfold P_Term. 
    intros x s.

    destruct (x =? y) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      exists s.
      apply S_Var1.
    + apply eqb_neq in Heqb as Hneq.
      exists (Var y).
      apply S_Var2.
      assumption.
      
  - (* TyAbs *)
    intros bX K t IHt. 
    unfold P_Term. 
    intros x s.

    assert (temp: exists t', substitute x s t t') by eauto.
    destruct temp as [t' Hsubst_t].
    
    eauto.

  - (* LamAbs *)
    intros bx T t IHt. 
    unfold P_Term. 
    intros x s.

    assert (temp: exists t', substitute x s t t') by eauto. 
    destruct temp as [t' Hsubst_t].
    
    assert ({x = bx} + {x <> bx}) by eauto using string_dec.
    
    destruct H.
    + subst.
      eauto.
    + eauto.

  - (* Apply *)
    intros t1 IHt1 t2 IHt2.
    unfold P_Term.
    intros x s.

    assert (temp: exists t1', substitute x s t1 t1') by eauto. 
    destruct temp as [t1' Hsubst_t1].
    assert (temp: exists t2', substitute x s t2 t2') by eauto. 
    destruct temp as [t2' Hsubst_t2].

    eauto.
Admitted.

Corollary substitute_models_total_function__Term : forall t x s, 
    exists t', substitute x s t t'.
Proof. apply substitute_models_total_function. Qed.

Corollary substitute_models_total_function__Binding : forall b x s,
    exists b', substitute_binding x s b b'.
Proof. apply substitute_models_total_function. Qed.

Corollary substitute_models_total_function__Bindings_NonRec : forall bs x s,
    exists bs', substitute_bindings_nonrec x s bs bs'.
Proof.
  intros.
  eapply P_Bindings_NonRec__holds_definitionally; eauto.
  assert (forall bs0, Util.ForallP P_Binding bs0). {
    induction bs0.
    - constructor.
    - constructor.
      + apply substitute_models_total_function.
      + assumption.
  }
  apply H.
Qed.

Corollary substitute_models_total_function__Bindings_Rec : forall bs x s,
    exists bs', substitute_bindings_rec x s bs bs'.
Proof.
  intros.
  eapply P_Bindings_Rec__holds_definitionally; eauto.
  assert (forall bs0, Util.ForallP P_Binding bs0). {
    induction bs0.
    - constructor.
    - constructor.
      + apply substitute_models_total_function.
      + assumption.
  }
  apply H.
Qed.