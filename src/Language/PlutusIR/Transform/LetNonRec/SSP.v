Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Definition P_has_type ctx t1 T := 
  forall t2, 
    CNR_Term t1 t2 -> 
    ctx |-+ t2 : T.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs1 :=
    forall bs2, (
      ctx |-oks_nr bs1 ->
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      ctx |-oks_nr bs2
    ) /\ (
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      map binds bs1 = map binds bs2
    ) /\ (
      forall f_bs2 t T,
        ctx |-oks_nr bs1 -> 
        CNR_Bindings bs1 f_bs2 ->
        (append (flatten (map binds bs1)) ctx) |-+ t : T ->
        ctx |-+ (fold_right apply t f_bs2) : T
    ).

Definition P_bindings_well_formed_rec ctx bs1 :=
  forall bs2, (
    ctx |-oks_r bs1 ->
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    ctx |-oks_r bs2
  ) /\ (
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    map binds bs1 = map binds bs2
  ).

Definition P_binding_well_formed ctx b1 := 
  forall b2, (
      ctx |-ok b1 ->
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      ctx |-ok b2
    ) /\ (
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      binds b1 = binds b2
    ) /\ (
      forall f_b2 t T,
        ctx |-ok b1 ->
        CNR_Binding b1 f_b2 ->
        (append (binds b1) ctx) |-+ t : T ->
        ctx |-+ (f_b2 t) : T  
    ).


Theorem CNR_Term__SSP : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P_has_type ctx t1 T.
Proof.
  apply has_type__ind with (P := P_has_type) (P0 := P_constructor_well_formed) (P1 := P_bindings_well_formed_nonrec) (P2 := P_bindings_well_formed_rec) (P3 := P_binding_well_formed).
  - (* T_Let *)
    intros. unfold P_has_type. intros.
    inversion X; subst.
    + apply H1.
      * apply bs.
      * assumption.
      * assumption.
      * apply H3.
        assumption.
    + inversion X0. subst. 
      eapply T_Let.
      * reflexivity.
      * apply H1. assumption. assumption.
      * unfold P_bindings_well_formed_rec in H2. edestruct H1 as [_ [Heq _]]. apply Heq in X1. rewrite <- X1. apply H3. assumption. 
  - (* T_LetRec *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    eapply T_LetRec.
    + reflexivity.
    + unfold P_bindings_well_formed_rec in H1.
      edestruct H1 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply IHH. auto. auto.
    + unfold P_bindings_well_formed_rec in H1.
      edestruct H1 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply H3.
      assumption.
  - (* T_Var *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Var. assumption.
  - (* T_TyAbs *)
    intros. unfold P_has_type. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyAbs.
    unfold P_has_type in H0.
    apply H0.
    apply X2.
  - (* T_LamAbs *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_LamAbs.
    + apply H0. assumption.
    + assumption.
  - (* T_Apply *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Apply with T1.
    + apply H0. assumption.
    + apply H2. assumption.
  - (* T_Constant *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Constant.
  - (* T_Builtin *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Builtin.
  - (* T_TyInst *)
    intros. unfold P_has_type. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyInst with (T1 := T1) (X := X) (K2 := K2) (T1' := T1').
    + apply H0. assumption.
    + assumption.
    + assumption.
    + assumption.
  - (* T_Error *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Error.
    apply H.
  - (* T_IWrap *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_IWrap with (K := K) (S := S).
    + assumption.
    + apply H1. assumption.
    + assumption.
    + assumption.
  - (* T_Unwrap *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Unwrap with (F := F) (K := K) (T := T).
    + apply H0. assumption.
    + assumption.
    + assumption.

  - (* T_ExtBuiltin *)
    intros. unfold P_has_type. intros.
    inversion X. subst.
    inversion X0.
    
  - (* W_Con *)
    intros. unfold P_constructor_well_formed. intros.
    eapply W_Con; eauto.
    
  - (* W_NilB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    split.
    + intros.
      inversion X. subst.
      assumption.
    + split.
      * intros.
        inversion X. subst.
        reflexivity.
      * intros.
        inversion X. subst.
        simpl in H0.
        rewrite flatten_nil in H0.
        rewrite append_emptyContext_l in H0.
        assumption.
  - (* W_ConsB_NonRec *)
    intros. unfold P_bindings_well_formed_nonrec. intros.
    split.
    + intros.
      inversion X. subst.
      apply W_ConsB_NonRec.
      * apply H0. assumption. assumption.
      * unfold P_binding_well_formed in H0.
        edestruct H0 as [_ [Heq _]].
        apply Heq in X0.
        rewrite <- X0.
        apply H2. assumption. assumption.
    + split.
      * intros.
        inversion X. subst.
        simpl.
        f_equal.
        -- apply H0. assumption.
        -- apply H2. assumption.
      * intros.
        inversion X. subst.
        inversion X0. subst.
        edestruct H2 as [_ [_ J]].
        
        simpl.
        edestruct H0 as [_ [_ J2]].
        apply J2.
        -- assumption.
        -- assumption.
        -- apply J.
           ++ assumption.
           ++ assumption.
           ++ simpl.
              simpl in H4.
              unfold flatten in H4.
              simpl in H4. 
              rewrite concat_append in H4.
              simpl in H4.
              rewrite <- append_assoc in H4.
              rewrite append_emptyContext_r in H4.
              simpl in H4.
              apply H4.
  - (* W_NilB_Rec *)
    intros. unfold P_bindings_well_formed_rec. intros.
    split.
    + intros.
      inversion X. subst.
      assumption.
    + intros.
      inversion X. subst.
      reflexivity.
  - (* W_ConsB_Rec*)
    intros. unfold P_bindings_well_formed_rec. intros.
    split.
    + intros.
      inversion X. subst.
      apply W_ConsB_Rec.
      * apply H0. assumption. assumption.
      * apply H2. assumption. assumption.
    + intros.
      inversion X. subst.
      simpl.
      f_equal.
      -- apply H0. assumption.
      -- apply H2. assumption.
           
  - (* W_Term *)
    intros. unfold P_binding_well_formed. intros.
    split.
    + intros. 
      inversion X. subst.
      apply W_Term.
      * assumption.
      * apply H1. assumption.
    + split. 
      * intros.
        inversion X. subst.
        reflexivity.
      * intros.
        inversion X. subst.
        eapply T_Apply.
        -- apply T_LamAbs.
          ++ simpl in H3.
             rewrite append_singleton_l in H3. 
             assumption. 
          ++ assumption.
        -- apply H1. assumption.
  - (* W_Type *)
    intros. unfold P_binding_well_formed. intros.
    split.
    + intros. 
      inversion X0. subst.
      apply W_Type.
      assumption.
    + split.
      * intros.
        inversion X0. subst.
        reflexivity.
      * intros.
        inversion X0.
  - (* W_Data *)
    intros. unfold P_binding_well_formed. intros.
    split.
    + intros.
      inversion X0. subst.
      assumption.
    + split.
      * intros.
        inversion X0. subst.
        reflexivity.
      * intros.
        inversion X0.

  Unshelve. auto. apply (TermBind Strict (VarDecl v ty) t_bound).
Qed. 
