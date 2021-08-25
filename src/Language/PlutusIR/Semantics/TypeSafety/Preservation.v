Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.


Lemma preservation__eval_defaultfun : forall ctx t T,
    ctx |-+ t : T ->
    forall v,
      eval_defaultfun t v ->
      ctx |-+ v : T.
Proof. Admitted. (* TODO *)

Theorem unique_kinds : forall ctx T K K',
    ctx |-* T : K ->
    ctx |-* T : K' ->
    K = K'.
Proof. Admitted.


Definition P_term ctx t T := 
  forall v, 
    t ==> v -> 
    ctx |-+ v : T.


Definition P_constructor ctx c := ctx |-ok_c c.

Definition P_bindings_nonrec ctx bs := 
  forall t0 T v0,
    ctx |-oks_nr bs ->    
    P_term (append (flatten (List.map binds bs)) ctx) t0 T ->
    eval_bindings_nonrec (Let NonRec bs t0) v0 ->
    append (flatten (List.map binds bs)) ctx |-+ t0 : T ->
    ctx |-+ v0 : T.

Definition P_bindings_rec ctx bs := ctx |-oks_r bs.

Definition P_binding ctx b := (*ctx |-ok b.*)
  forall s x Tb tb vb t t' T,
    b = TermBind s (VarDecl x Tb) tb ->
    (binds (TermBind s (VarDecl x Tb) tb) ++ ctx) |-+ t : T ->
    substitute x vb t t' ->
    ctx |-+ t' : T.

Axiom skip : forall P, P.

Theorem preservation' : forall (t : Term) (T : Ty),
  empty |-+ t : T ->
  P_term empty t T. 
Proof.
  intros.
  eapply has_type__ind with (P := P_term) (P0 := P_constructor) (P1 := P_bindings_nonrec) (P2 := P_bindings_rec) (P3 := P_binding).
  - intros. unfold P_term. intros.
    inversion H5; subst.
    unfold P_bindings_nonrec in H3.
    eapply H2.
    + apply H1.
    + apply H4.
    + apply H9.
    + apply H3.
  - apply skip. (* TODO *)
  - (* T_Var *)
    intros. unfold P_term. intros.
    inversion H1. 
  - (* T_TyAbs *)
    intros. unfold P_term. intros.
    inversion H2. subst.
    apply T_TyAbs.
    apply H1.
    assumption.
  - (* T_LamAbs *)
    intros. unfold P_term. intros.
    inversion H3. subst.
    apply T_LamAbs.
    + assumption.
    + assumption.
  - (* T_Apply *) 
    intros. unfold P_term. intros.
    inversion H4.
    + subst. apply skip. (* TODO *)
    + subst. 
      apply T_Apply with T1.
      * apply H1.
        assumption.
      * apply H3.
        assumption.   
    + subst.
      apply preservation__eval_defaultfun with (Apply v1 v2).
      * apply T_Apply with T1.
        -- apply H1.
           assumption.
        -- apply H3.
           assumption.
      * assumption.
  - (* T_Constant *)
    intros. unfold P_term. intros.
    inversion H0. subst.
    apply T_Constant.
  - (* T_Builtin *)
    intros. unfold P_term. intros.
    inversion H0. subst.
    apply T_Builtin.
  - (* T_TyInst *) 
    intros. unfold P_term. intros.
    inversion H4.
    + subst.
      apply T_TyInst with (T1 := T1) (X := X) (K2 := K2).
      * apply H1.
        assumption.
      * assumption.
      * assumption.
    + subst. apply skip. (* TODO *)
  - (* T_Error *)
    intros. unfold P_term. intros.
    inversion H1. subst.
    apply T_Error.
    assumption.
  - (* T_IWrap *)
    intros. unfold P_term. intros.
    inversion H5. subst.
    apply T_IWrap with (X := X) (K := K) (S := S).
    + assumption.
    + apply H2.
      assumption.
    + assumption.
    + assumption.
  - (* T_Unwrap *)
    intros. unfold P_term. intros.
    inversion H4. subst.
    apply H1 in H6 as H7.
    inversion H7. subst.
    assert (K = K0) by eauto using unique_kinds.
    subst. (* TODO: something with transitivity and free variables *)
    apply skip.

  - (* W_Con *)
    intros. unfold P_constructor. 
    apply W_Con.
    assumption.

  - intros. unfold P_bindings_nonrec. intros.
    inversion H2. subst.
    simpl in H3.
    unfold P_term in H1.
    simpl in H1.
    apply H1.
    apply H5.
  - intros. unfold P_bindings_nonrec. unfold P_bindings_nonrec in H3. intros.
    inversion H6. subst.

    eapply H1.
    + reflexivity.
    + simpl.
      eapply H3.
      * assumption.
      * unfold flatten in H5.
        unfold flatten in H5.
        unfold append in H5.
        simpl in H5. unfold extendT in H5. simpl in H5.
        rewrite List.concat_app in H5. simpl in H5.
        rewrite <- List.app_assoc in H5. simpl in H5.
        apply H5.
      * apply skip. 
      * unfold flatten in H7.
        unfold flatten in H7.
        unfold append in H7.
        simpl in H7. unfold extendT in H7. simpl in H7.
        rewrite List.concat_app in H7. simpl in H7.
        rewrite <- List.app_assoc in H7. simpl in H7.
        apply H7.
Abort.

Theorem preservation : forall t v T,
    empty |-+ t : T ->
    t ==> v ->
    empty |-+ v : T.
Proof. Admitted.