Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
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

  Abort.


Theorem progress : forall (t : Term) (T : Ty),
    emptyContext |-+ t : T ->
    exists v, t ==> v.
Proof. Abort.


Module e.

Definition P_has_type (ctx : Context) (t : Term) (T : Ty) :=
  ctx = emptyContext ->
  (exists v, t ==> v) \/
  ~(exists v, t ==> v).

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs := 
  forall t T,
    ctx |-oks_nr bs ->
    (append (flatten (map binds bs)) ctx) |-+ t : T ->
    (exists v, eval_bindings_nonrec (Let NonRec bs t) v) \/
    ~(exists v, eval_bindings_nonrec (Let NonRec bs t) v).

Definition P_bindings_well_formed_rec ctx bs := ctx |-oks_r bs.

Definition P_binding_well_formed (ctx : Context) b :=
  forall s x Tb tb,
    b = TermBind s (VarDecl x Tb) tb ->
    exists vb, tb ==> vb.

Axiom skip : forall P, P.

Theorem preservation : forall t v T,
    emptyContext |-+ t : T ->
    t ==> v ->
    emptyContext |-+ v : T.
Proof. Admitted.

Theorem progress' : forall (t : Term) (T : Ty) ,
  emptyContext |-+ t : T ->
  P_has_type emptyContext t T.
Proof.
  apply has_type__ind with P_constructor_well_formed P_bindings_well_formed_nonrec P_bindings_well_formed_rec P_binding_well_formed.
  - intros. unfold P_has_type. intros.
    subst.
    destruct (H1 _ _ H0 H2). 
    + destruct H.
      left.
      exists x.
      apply E_Let.
      assumption.
    + right.
      intros Hcon.
      apply H.
      destruct Hcon.
      exists x.
      inversion H4.
      subst.
      assumption. 
  - intros. unfold P_has_type.
    apply skip.
  - intros. unfold P_has_type. intros.
    subst. left. inversion H.
  - intros. unfold P_has_type. intros.
    apply skip.
  - intros. unfold P_has_type. intros.
    subst.
    left.
    exists (LamAbs x T1 t).
    apply E_LamAbs.
  - (* T_Apply *)
    intros. unfold P_has_type. intros.
    subst.
    assert (emptyContext = emptyContext) by reflexivity.
    apply H0 in H3 as H4.
    apply H2 in H3 as H5.
    destruct H4; destruct H5.
    + destruct H4. destruct H5.
      eapply preservation in H4 as H6; eauto.
      apply eval_to_value in H4 as H7.
      inversion H6; subst; inversion H7; subst; try solve [inversion H8; subst].
      * assert (forall x s t6 t6', value s -> substitute x s t6 t6' -> (exists v, t6' ==> v) \/ ~(exists v, t6' ==> v)). {
          apply skip.
        }
        apply eval_to_value in H5 as H9.
        assert (exists t', substitute x1 x0 t t'). {
          apply skip.
        }
        destruct H10.
        eapply H8 in H9 as H14; try solve [apply H10].
        destruct H14.
        -- destruct H11.
           left.
           exists x2.
           eapply E_Apply.
           ++ apply H4.
           ++ apply H5.
           ++ apply H10.
           ++ apply H11.
Abort.