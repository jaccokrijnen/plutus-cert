Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Definition P_Term (t : Term) :=
  forall x,
    ~(appears_free_in_Annotation x t) ->
    forall s t', 
      substituteA x s t t' ->
      t' = t.

Definition P_Binding (b : Binding) :=
  forall x,
    ~(appears_free_in_Annotation__binding x b) ->
    forall s b',
      substituteA_binding x s b b' ->
      b' = b.

Definition P_Bindings_NonRec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_Annotation__bindings_nonrec x bs) ->
    forall s bs',
      substituteA_bindings_nonrec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_NonRec. intros.
    inversion H0.
    + subst.
      f_equal.
      apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFIA_ConsB1_NonRec.
        assumption.
      * assumption.
    + subst.
      f_equal.
      * apply Util.ForallT_hd in X.
        unfold P_Binding in X.
        apply X with x s.
        -- intros Hcon.
           apply H.
           apply AFIA_ConsB1_NonRec.
           assumption.
        -- assumption.
      * unfold P_Bindings_NonRec in IHbs.
        apply IHbs with x s.
        -- apply Util.ForallT_tl in X.
           assumption.
        -- intros Hcon.
           apply H.
           apply AFIA_ConsB2_NonRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
Qed.

Definition P_Bindings_Rec (bs : list Binding) :=
  Util.ForallT P_Binding bs ->
  forall x,
    ~(appears_free_in_Annotation__bindings_rec x bs) ->
    forall s bs',
      substituteA_bindings_rec x s bs bs' ->
      bs' = bs.

Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec. intros.
    inversion H0. subst.
    reflexivity.
  - unfold P_Bindings_Rec. intros.
    inversion H0.
    subst.
    f_equal.
    + apply Util.ForallT_hd in X.
      unfold P_Binding in X.
      apply X with x s.
      * intros Hcon.
        apply H.
        apply AFIA_ConsB1_Rec.
        assumption.
      * assumption.
    + unfold P_Bindings_Rec in IHbs.
      apply IHbs with x s.
      * apply Util.ForallT_tl in X.
        assumption.
      * intros Hcon.
        apply H.
        apply AFIA_ConsB2_Rec.
        assumption.
      * assumption.
Qed.

Lemma vacuous_substituteA : forall t, P_Term t.
Proof.
  apply Term_rect' with (P := P_Term) (Q := P_Binding).
  - (* Let *)
    intros. unfold P_Term. intros.
    inversion H1; subst.
    + (* S_Let1 *)
      f_equal.
      assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
      unfold P_Bindings_NonRec in H2.
      apply H2 with x s.
      * assumption.
      * intros Hcon.
        apply H0.
        apply AFIA_LetNonRec.
        assumption.
      * assumption.
    + (* S_Let2 *)
      f_equal.
      * assert (P_Bindings_NonRec bs) by apply P_Bindings_NonRec__holds_definitionally.
        unfold P_Bindings_NonRec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFIA_LetNonRec.
           assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFIA_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
    + (* S_LetRec1 *)
      reflexivity.
    + (* S_LetRec2 *)
      f_equal.
      * assert (P_Bindings_Rec bs) by apply P_Bindings_Rec__holds_definitionally.
        unfold P_Bindings_Rec in H2.
        apply H2 with x s.
        -- assumption.
        -- intros Hcon.
           apply H0.
           apply AFIA_LetRec.
           ++ assumption.
           ++ assumption.
        -- assumption.
      * unfold P_Term in H.
        apply H with x s.
        -- intros Hcon.
           apply H0.
           apply AFIA_Let.
           ++ assumption.
           ++ assumption.
        -- assumption.
  - (* Var *)
    intros. unfold P_Term. intros.
    inversion H0.
    subst.
    reflexivity.
  - (* TyAbs *)
    intros. unfold P_Term. intros.
    inversion H1.
    + subst.
      reflexivity.
    + subst.
      f_equal.
      eapply H; eauto.
  - (* LamAbs *)
    intros. unfold P_Term. intros.
    inversion H1.
    subst.
    f_equal.
    (*
    + apply skip.
    + eapply H; eauto. 
    
      eapply 
    + (* S_LamAbs1 *)
      reflexivity.
    + (* S_LamAbs2 *)
      subst.
      f_equal.
      unfold P_Term in H.
      apply H with x s0.
      * intros Hcon.
        apply H0.
        apply AFIA_LamAbs.
        -- assumption.
        -- assumption.
      * assumption.
  - (* Apply *)
    intros. unfold P_Term. intros.
    inversion H2. subst.
    f_equal.
    + unfold P_Term in H. 
      apply H with x s.
      * intros Hcon.
        apply H1.
        apply AFIA_Apply1.
        assumption.
      * assumption.
    + unfold P_Term in H0.
      apply H0 with x s.
      * intros Hcon.
        apply H1.
        apply AFIA_Apply2.
        assumption.
      * assumption.
  - (* Constant *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* Builtin *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* TyInst *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFIA_TyInst.
      assumption.
    + assumption.
  - (* Error *)
    intros. unfold P_Term. intros.
    inversion H0. subst.
    reflexivity.
  - (* IWrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFIA_IWrap.
      assumption.
    + assumption.
  - (* Unwrap *)
    intros. unfold P_Term. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s.
    + intros Hcon.
      apply H0.
      apply AFIA_Unwrap.
      assumption.
    + assumption.

  - (* TermBind *)
    intros. unfold P_Binding. intros.
    inversion H1. subst.
    f_equal.
    unfold P_Term in H.
    apply H with x s0.
    + intros Hcon.
      apply H0.
      apply AFIA_TermBind.
      assumption.
    + assumption.
  - (* TypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
  - (* DatatypeBind *)
    intros. unfold P_Binding. intros.
    inversion H0. subst.
    reflexivity.
Qed.*)
Admitted.