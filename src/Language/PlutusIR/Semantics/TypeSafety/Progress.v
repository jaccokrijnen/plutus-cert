Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

Require Import Coq.Lists.List.

Definition P_has_type (ctx : Context) (t : Term) (T : Ty) :=
  ctx = emptyContext ->
  exists v, 
    t ==> v.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs := 
  forall t T,
    ctx |-oks_nr bs ->
    (append (flatten (map binds bs)) ctx) |-+ t : T ->
    exists v, eval_bindings_nonrec (Let NonRec bs t) v.

Definition P_bindings_well_formed_rec ctx bs := ctx |-oks_r bs.

Definition P_binding_well_formed (ctx : Context) b :=
  forall s x Tb tb,
    b = TermBind s (VarDecl x Tb) tb ->
    exists vb, tb ==> vb.

Axiom skip : forall P, P.

Lemma terminates : forall t v,
  t ==> v ->
  value v.
Proof. Admitted.

Theorem progress' : forall (t : Term) (T : Ty) ,
  emptyContext |-+ t : T ->
  P_has_type emptyContext t T.
Proof.
  apply has_type__ind with P_constructor_well_formed P_bindings_well_formed_nonrec P_bindings_well_formed_rec P_binding_well_formed.
  - intros. unfold P_has_type.
    subst.
    destruct (H1 _ _ H0 H2).
    exists x.
    apply E_Let.
    assumption.
  - intros. unfold P_has_type.
    apply skip.
  - intros. unfold P_has_type. intros.
    subst. inversion H.
  - intros. unfold P_has_type. intros.
    eexists.
    apply skip.
  - intros. unfold P_has_type. intros.
    exists (LamAbs x T1 t).
    apply E_LamAbs.
  - (* T_Apply *)
    intros. unfold P_has_type. intros.
    eexists.
    subst.
    assert (emptyContext = emptyContext) by reflexivity.
    apply H0 in H3 as H4.
    apply H2 in H3 as H5.
    destruct H5.
    destruct H4.
    apply terminates in H5 as H6.
    apply terminates in H4 as H7.
    inversion H6.
    + subst.

  Admitted.


Theorem progress : forall (t : Term) (T : Ty),
    emptyContext |-+ t : T ->
    exists v, t ==> v.
Proof. Admitted.