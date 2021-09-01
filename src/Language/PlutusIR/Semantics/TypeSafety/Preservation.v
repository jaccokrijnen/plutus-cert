Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.

Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.


Lemma preservation__compute_defaultfun : forall t T,
    emptyContext |-+ t : T ->
    forall v,
      compute_defaultfun t = Datatypes.Some v ->
      emptyContext |-+ v : T.
Proof.
  intros.
  destruct t; inversion H0.
  destruct t1; inversion H0. {
    destruct t1_1; inversion H0. {
      destruct t1_1_1; inversion H0. 
      destruct d; inversion H0.
      destruct t1_1_2; inversion H0.
      destruct s; inversion H0.
      destruct u; inversion H0.
      destruct v0; inversion H0.
      destruct t1_2; inversion H0.
      destruct s; inversion H0.
      destruct u0; inversion H0.
      destruct v0; inversion H0.
      destruct t2; inversion H0.
      destruct s; inversion H0.
      destruct u1; inversion H0.
      destruct v0; inversion H0.
      inversion H. subst.
      inversion H23; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H20.
      subst.
      inversion H21; subst.
      inversion H24; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H22.
      subst.
      inversion H20; subst.
      inversion H26; subst.
      apply Eqdep.EqdepTheory.inj_pair2 in H25.
      subst.
      inversion H22; subst.
      apply T_Constant.
    }
Admitted. (* TODO *)

Theorem unique_kinds : forall ctx T K K',
    ctx |-* T : K ->
    ctx |-* T : K' ->
    K = K'.
Proof. Admitted.


Definition P_eval (t v : Term) :=
  forall T,
    emptyContext |-+ t : T ->
    emptyContext |-+ v : T.

Definition P_eval_bindings_nonrec (t v : Term) :=
  forall bs t0,
    t = Let NonRec bs t0 ->
    forall T,
      emptyContext |-+ t : T ->
      emptyContext |-+ v : T.

Definition P_eval_bindings_rec (bs0 : list Binding) (t v : Term) :=
  forall bs t0,
    t = Let Rec bs t0 ->
    forall T,
      emptyContext |-+ t : T ->
      emptyContext |-+ v : T.


Axiom skip : forall P, P.

Lemma e : forall T T3 T2 T1 T0,
  substituteT "a" T (Ty_Fun (Ty_Builtin (Some (TypeIn DefaultUniBool))) (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "a") (Ty_Var "a")))) =b
    Ty_Fun T3 (Ty_Fun T2 (Ty_Fun T1 T0)) -> 
  T1 =b T2.
Proof.
  intros.
  simpl in H.
  induction H; auto.
  - apply skip.
  - apply skip.
Qed.


Theorem preservation' : 
  (forall (t v : Term), t ==> v -> P_eval t v) /\
  (forall (t v : Term), eval_bindings_nonrec t v -> P_eval_bindings_nonrec t v) /\
  (forall (bs0 : list Binding) (t v : Term), eval_bindings_rec bs0 t v -> P_eval_bindings_rec bs0 t v). 
Proof.
  apply eval__multind with
    (P := P_eval)
    (P0 := P_eval_bindings_nonrec)
    (P1 := P_eval_bindings_rec).
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
  - intros. unfold P_eval. intros.
    eapply H0; eauto.
  - (* E_TyAbs *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    apply T_TyAbs.
    apply skip.
  - intros. unfold P_eval. intros.
    assumption. 
  - intros. unfold P_eval. intros.
    inversion H6. subst.
    apply H0 in H10.
    apply H2 in H12.
    eapply substitution_preserves_typing in H3; eauto.
    inversion H10. subst.
    eauto.
  - intros. unfold P_eval. intros.
    assumption.
  - intros. unfold P_eval. intros.
    assumption.
  - intros. unfold P_eval. intros.
    inversion H5. subst.
    apply T_Apply with T1.
    + apply H0.
      assumption. 
    + apply H3.
      assumption.
  - intros. unfold P_eval. intros.
    inversion H6. subst.
    eapply preservation__compute_defaultfun.
    + apply T_Apply with T1. 
      * apply H0.
        assumption.
      * apply H3.
        assumption.
    + assumption.
  - intros. unfold P_eval. intros.
    inversion H1; subst.
    eapply T_TyInst; eauto.
  - intros. unfold P_eval. intros.
    inversion H3; subst.
    eapply T_Apply; eauto.
  - intros. unfold P_eval. intros.
    inversion H1; subst.
    eapply T_Apply; eauto.
  - intros. unfold P_eval. intros.
    inversion H3; subst.
    apply H0 in H7.
    apply H2.

    inversion H7. subst.
    inversion H8. subst.
    inversion H10; subst.
    inversion H6. subst.
    simpl in H16.
    
    apply skip. (* TODO *)
  - intros. unfold P_eval. intros.
    inversion H3. subst.
    apply H0 in H7.
    apply H2.

    inversion H7. subst.
    inversion H8. subst.
    inversion H10. subst.
    inversion H6. subst.
    simpl in H16.

    apply skip. (* TODO *)
  - intros. unfold P_eval. intros.
    inversion H1. subst.
    apply skip. (* TODO *)
  - intros. unfold P_eval. intros.
    assumption.
  - intros. unfold P_eval. intros.
    inversion H1. subst.
    eapply T_IWrap; eauto.
  - intros. unfold P_eval. intros.
    inversion H1. subst.
    apply H0 in H3.
    inversion H3. subst.
    apply skip. (* TODO *)

  - (* E_NilB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H1. subst.
    inversion H2. subst.
    simpl in H9.
    rewrite flatten_nil in H9.
    rewrite append_emptyContext_l in H9.
    apply H0.
    assumption.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H5. subst.
    inversion H6. subst.
    eapply H4.
    + reflexivity.
    + eapply T_Let.
      * reflexivity.
      * eapply substitution_preserves_typing__Bindings_NonRec.
        -- inversion H11. subst.
           simpl in H12.
           rewrite append_emptyContext_r in H12.
           apply H12.
        -- inversion H11. subst.
           inversion H10. subst.
           apply H0.
           assumption.
        -- assumption.
      * eapply substitution_preserves_typing.
        -- simpl in H13.
           erewrite <- append_extendT_permute.
           ++ rewrite flatten_extract in H13.
              rewrite append_emptyContext_r in H13.
              assert (List.map binds bs = List.map binds bs'). {
                eapply substitution_preserves_typing__Bindings_NonRec.
                - inversion H11. subst.
                  simpl in H12.
                  rewrite append_emptyContext_r in H12.
                  apply H12.
                - inversion H11. subst.
                  inversion H10. subst.
                  apply H0.
                  assumption.
                - assumption.
              }
              rewrite <- H7.
              apply H13.
           ++ apply skip. (* TODO *)
        -- inversion H11. subst.
           inversion H10. subst.
           apply H0.
           assumption.
        -- assumption.

  - (* E_NilB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H1. subst.
    
Abort.

Theorem preservation : forall t v T,
    emptyContext |-+ t : T ->
    t ==> v ->
    emptyContext |-+ v : T.
Proof. Abort.