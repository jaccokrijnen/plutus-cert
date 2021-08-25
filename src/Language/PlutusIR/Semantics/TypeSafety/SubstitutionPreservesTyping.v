Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Weakening.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import Coq.Strings.String.

Axiom skip : forall P, P.

Definition P_Term (t : Term) :=
  forall ctx x U v T t',
    extendT x U ctx |-+ t : T ->
    emptyContext |-+ v : U ->
    substitute x v t t' ->
    ctx |-+ t' : T.
#[export] Hint Unfold P_Term : core.

Definition P_Binding (b : Binding) :=
  forall ctx x U v b',
    extendT x U ctx |-ok b ->
    emptyContext |-+ v : U ->
    substitute_binding x v b b' ->
    ctx |-ok b' /\ binds b = binds b'.
#[export] Hint Unfold P_Binding : core.

Definition P_Bindings_NonRec (bs : list Binding) :=
  forall ctx x U v bs',
    extendT x U ctx |-oks_nr bs ->
    emptyContext |-+ v : U ->
    Util.ForallT P_Binding bs ->
    substitute_bindings_nonrec x v bs bs' ->
    ctx |-oks_nr bs'.

Lemma e : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H1. subst.
    auto with typing.
  - unfold P_Bindings_NonRec.
    intros.
    inversion H1.
    + subst.
      apply W_ConsB_NonRec.
      * apply Util.ForallT_hd in X.
        unfold P_Binding in X.
        eapply X.
        -- inversion H. subst.
           apply H5.
        -- apply H0.
        -- assumption.
      * apply Util.ForallT_hd in X.
        unfold P_Binding in X.
        inversion H. subst.
        destruct (X _ _ _ _ _ H5 H0 H8).
        rewrite <- H3.
        apply skip.
    + subst.
      apply W_ConsB_NonRec.
      * apply Util.ForallT_hd in X.
        apply X with x U v.
        -- inversion H. subst.
           assumption.
        -- assumption.
        -- assumption.
      * eapply IHbs.
        -- inversion H. subst.
           apply skip.
        -- apply H0.
        -- apply Util.ForallT_tl in X.
           assumption.
        -- apply H9.
Qed.

Lemma substitution_preserves_typing : forall t, P_Term t.
Proof.
  apply Term_rect' with (P := P_Term) (Q := P_Binding).
  - intros. autounfold. intros.
    inversion H2.
    + subst.
      eapply T_Let.
      * reflexivity.
      * eapply e.
        -- inversion H0. subst.
            eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * inversion H0. subst.
        apply skip.
    + subst.
      inversion H0. subst.
      eapply T_Let.
      * reflexivity.
      * eapply e.
        -- inversion H0. subst.
           eauto.
        -- eauto.
        -- eauto.
        -- eauto.
      * apply skip.
    + apply skip.
    + apply skip.
  - intros. autounfold. intros.
    inversion H1.
    + subst.
      inversion H.
      subst.
      inversion H4.
      rewrite update_eq in H3.
      inversion H3. subst. 
      eapply weakening_empty; eauto.
    + subst.
      apply T_Var.
      inversion H.
      subst.
      simpl in H4.
      rewrite update_neq in H4; auto.
  - (* TyAbs *) 
    intros. autounfold. intros.
    inversion H2. subst.
    inversion H0. subst.
    apply T_TyAbs.
    rewrite extendT_extendK_permute in H8.
    eapply H.
    + eauto.
    + eauto.
    + eauto.
  - (* LamAbs *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2.
    + subst.
      apply T_LamAbs.
      * rewrite extendT_shadow in H8.
        assumption.
      * apply skip.
    + subst.
      apply T_LamAbs.
      * eapply H.
        -- rewrite extendT_permute in H8; auto.
           apply H8.
        -- eassumption.
        -- assumption.
      * apply skip.
  - (* Apply *)
    intros. autounfold. intros.
    inversion H1. subst.
    inversion H3. subst.
    eapply T_Apply.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + eapply H0.
      * eassumption.
      * eassumption.
      * assumption.
  - (* Constant *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Constant.
  - (* Builtin *) 
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Builtin.
  - (* TyInst *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_TyInst.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + apply skip.
    + assumption.
  - (* Error *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    apply T_Error.
    apply skip.
  - (* IWrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_IWrap.
    + eassumption.
    + eapply H.
      * eassumption.
      * eassumption.
      * eassumption.
    + apply skip.
    + apply skip.
  - (* Unwrap *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst.
    eapply T_Unwrap.
    + eapply H.
      * eassumption.
      * eassumption.
      * assumption.
    + apply skip.
    + eassumption.

  - (* TermBind *)
    intros. autounfold. intros.
    inversion H0. subst.
    inversion H2. subst. 
    split.
    + apply W_Term.
      * apply skip.
      * eapply H.
        -- eassumption.
        -- eassumption.
        -- assumption.
    + reflexivity. 
  - (* TypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split. 
    + apply W_Type.
      apply skip.
    + reflexivity.
  - (* DatatypeBind *)
    intros. autounfold. intros.
    inversion H. subst.
    inversion H1. subst.
    split.
    + eapply W_Data.
      * reflexivity.
      * intros.
        apply skip.
    + reflexivity.
Qed.
