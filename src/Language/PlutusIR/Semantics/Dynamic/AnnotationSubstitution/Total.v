Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Import PlutusCert.Util.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.

Definition P_Term (t : Term) : Prop :=
  forall x s,
    exists t', substituteA x s t t'.

Definition P_Binding (b : Binding) : Prop :=
  forall x s,
    exists b', substituteA_binding x s b b'.

Definition P_Bindings_NonRec (bs : list Binding) : Prop :=
  forall x s,
    ForallP P_Binding bs ->
    exists bs', substituteA_bindings_nonrec x s bs bs'.

Definition P_Bindings_Rec (bs : list Binding) : Prop :=
  forall x s,
    ForallP P_Binding bs ->
    exists bs', substituteA_bindings_rec x s bs bs'.

Lemma P_Bindings_NonRec__holds_definitionally : forall bs, P_Bindings_NonRec bs.
Proof.
  induction bs.
  - unfold P_Bindings_NonRec. intros.
    exists nil.
    apply SA_NilB_NonRec.
  - rename a into b. 
    unfold P_Bindings_NonRec. intros.
    apply ForallP_uncons in H.
    destruct H.
    destruct p with x s.
    rename x0 into b'.
    assert (exists bs', substituteA_bindings_nonrec x s bs bs') by eauto.
    destruct H0 as [bs' H0].

    assert ({In x (tyvars_bound_by_binding b)} + {~ In x (tyvars_bound_by_binding b)}) by eauto using in_dec, string_dec.
    destruct H1.
    + exists (b' :: bs).
      apply SA_ConsB_NonRec1; auto.
    + exists (b' :: bs').
      apply SA_ConsB_NonRec2; auto.
Qed. 


Lemma P_Bindings_Rec__holds_definitionally : forall bs, P_Bindings_Rec bs.
Proof.
  induction bs.
  - unfold P_Bindings_Rec. intros.
    exists nil.
    apply SA_NilB_Rec.
  - rename a into b. 
    unfold P_Bindings_Rec. intros.
    apply ForallP_uncons in H.
    destruct H.
    destruct p with x s.
    rename x0 into b'.
    assert (exists bs', substituteA_bindings_rec x s bs bs') by eauto.
    destruct H0 as [bs' H0].

    exists (b' :: bs').
    apply SA_ConsB_Rec; auto.
Qed.

Lemma substituteA_total : 
  (forall t, P_Term t) /\ (forall b, P_Binding b).
Proof. Admitted.


Lemma msubstA_total : 
  (forall envA t, exists t', msubstA envA t t').
Proof.
  induction envA; intros.
  - exists t. constructor.
  - destruct a as [a T].
    assert (exists t', substituteA a T t t') by (eapply substituteA_total; eauto).
    destruct H as [t' Hsa__t'].
    destruct (IHenvA t') as [t'' Hmsa__t''].
    exists t''.
    econstructor.
    + apply Hsa__t'.
    + apply Hmsa__t''.
Qed.