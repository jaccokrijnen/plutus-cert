Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Import PlutusCert.Util.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.


(** * Predicates *)

Definition P_Term (t : Term) : Prop :=
  forall x s,
    exists t', substitute x s t t'.

Definition P_Binding (b : Binding) : Prop :=
  forall x s,
    exists b', substitute_binding x s b b'.

(** * Helper lemmas *)
Lemma P_letnonrec : forall bs x s t,
    P_Term t ->
    ForallP P_Binding bs ->
    exists bs' t', substitute x s (Let NonRec bs t) (Let NonRec bs' t').
Proof.
  induction bs.
  - intros.
    unfold P_Term in H.
    destruct (H x s) as [t' Hs__t'].
    eauto.
  - rename a into b. 
    intros.
    apply ForallP_uncons in H0.
    destruct H0.
    destruct p with x s.
    rename x0 into b'.

    eapply IHbs in f; eauto.
    destruct f as [bs' [t' Hs]].

    
    assert ({In x (bound_vars_in_binding b)} + {~ In x (bound_vars_in_binding b)}) by eauto using in_dec, string_dec.
    destruct H1.
    + exists (b' :: bs), t. apply S_LetNonRec_Cons1. all: eauto.
    + exists (b' :: bs'), t'. apply S_LetNonRec_Cons2. all: eauto. 
Qed. 

Lemma P_letrec : forall bs x s t,
    P_Term t ->
    ForallP P_Binding bs ->
    exists bs' t', substitute_letrec x s (Let Rec bs t) (Let Rec bs' t').
Proof.
  induction bs.
  - intros.
    unfold P_Term in H.
    destruct (H x s) as [t' Hs__t'].
    eauto.
  - rename a into b. 
    intros.
    apply ForallP_uncons in H0.
    destruct H0.
    destruct p with x s.
    rename x0 into b'.

    eapply IHbs in f; eauto.
    destruct f as [bs' [t' Hs]].

    eauto.
Qed.

Lemma substitute__total : 
  (forall t, P_Term t) /\ 
  (forall b, P_Binding b).
Proof.
  apply Term__multind with (P := P_Term) (Q := P_Binding).
  - (* Let *)
    intros rec bs t FPbs IHt. 
    unfold P_Term. 
    intros x s.

    assert (temp: exists bs' t', substitute x s (Let NonRec bs t) (Let NonRec bs' t')) by (eapply P_letnonrec; eauto).
    destruct temp as [bs'_nr [t'_nr Hs_nr]].
    assert (temp: exists bs' t', substitute_letrec x s (Let Rec bs t) (Let Rec bs' t')) by (eapply P_letrec; eauto).
    destruct temp as [bs'_r [t'r H_r]].

    assert ({In x (bound_vars_in_bindings bs)} + {~ In x (bound_vars_in_bindings bs)}) 
      by eauto using in_dec, string_dec.

    all: destruct rec.
    all: destruct H.
    all: eauto.

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
  - (* Constant *)
Admitted.

Corollary substitute_term__total : forall t x s, 
    exists t', substitute x s t t'.
Proof. apply substitute__total. Qed.

Corollary substitute_binding__total : forall b x s,
    exists b', substitute_binding x s b b'.
Proof. apply substitute__total. Qed.

Lemma msubst_term__total : forall env t,
    exists t', msubst_term env t t'.
Proof.
  induction env; intros.
  - exists t. constructor.
  - destruct a as [a T].
    assert (exists t', substitute a T t t') by (eapply substitute_term__total; eauto).
    destruct H as [t' Hs__t'].
    destruct (IHenv t') as [t'' Hms__t''].
    exists t''.
    econstructor.
    + apply Hs__t'.
    + apply Hms__t''.
Qed.

Lemma msubst_binding__total : forall env b,
    exists b', msubst_binding env b b'.
Proof.
  induction env; intros.
  - exists b. constructor.
  - destruct a as [a T].
    assert (exists b', substitute_binding a T b b') by (eapply substitute_binding__total; eauto).
    destruct H as [b' Hs__b'].
    destruct (IHenv b') as [b'' Hms__b''].
    exists b''.
    econstructor.
    + apply Hs__b'.
    + apply Hms__b''.
Qed.