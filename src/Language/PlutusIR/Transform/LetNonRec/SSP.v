Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require PlutusCert.Language.PlutusIR.Semantics.Static.
Require PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.DeBruijn.
Require PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.

Require Import PlutusCert.Language.PlutusIR.Conversion.

Module DB.

Import PlutusCert.Language.PlutusIR.Semantics.Static.
Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.DeBruijn.
Import DeBruijnTerm.
Import ConvertInductive.

Definition P ctx t1 T := 
  forall t2 t1' t2' vars, 
    CNR_Term t1' t2' -> 
    ConvertTerm vars t1' t1 ->
    ConvertTerm vars t2' t2 ->
    ctx |-+ t2 : T.

Definition Q ctx c := ctx |-ok_c c.

Definition R ctx b1 := 
  forall b2 b1' b2' vars,
    Congruence.Cong_Binding CNR_Term b1' b2' ->
    ConvertBinding vars b1' b1 ->
    ConvertBinding vars b2' b2 ->
    ctx |-ok b2.

(*
Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P ctx t1 T.
Proof.
  apply has_type_rec with (P := P) (P0 := Q) (P1 := R).
  - intros.  
    unfold P.
    intros.
    inversion H4. subst.
    inversion X; subst.
    + apply skip.
    + inversion X0. subst. apply skip.
  - intros.
    unfold P.
    intros.
    inversion H5. subst.
    rename bs0 into bs1'. rename t0 into t1'. rename bs into bs1. rename t into t1.
    inversion X. subst.
    inversion X0. subst.
    rename bs' into bs2'. rename t' into t2'.
    inversion H6. subst.
    rename bs' into bs2. rename t0' into t2.
    eapply T_LetRec.
    + auto.
    + reflexivity.
    + intros.
      unfold R in H2.
Abort.

*)

End DB.



Module Named.

Import PlutusCert.Language.PlutusIR.Semantics.Static.
Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Import NamedTerm.

Definition P_term ctx t1 T := 
  forall t2, 
    CNR_Term t1 t2 -> 
    ctx |-+ t2 : T.

Definition P_constructor ctx c := ctx |-ok_c c.

Definition P_bindings_nonrec ctx bs1 :=
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
        ((flatten (map binds bs1)) ++ ctx) |-+ t : T ->
        ctx |-+ (fold_right apply t f_bs2) : T
    ).

Definition P_bindings_rec ctx bs1 :=
  forall bs2, (
    ctx |-oks_r bs1 ->
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    ctx |-oks_r bs2
  ) /\ (
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    map binds bs1 = map binds bs2
  ).

Definition P_binding ctx b1 := 
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
        (binds b1 ++ ctx) |-+ t : T ->
        ctx |-+ (f_b2 t) : T  
    ).


Theorem CNR_Term__preserves_typing : forall ctx t1 T,
    ctx |-+ t1 : T ->
    P_term ctx t1 T.
Proof.
  apply has_type__ind with (P := P_term) (P0 := P_constructor) (P1 := P_bindings_nonrec) (P2 := P_bindings_rec) (P3 := P_binding).
  - (* T_Let *)
    intros. unfold P_term. intros.
    inversion X; subst.
    + replace ctx with ([] ++ ctx) by reflexivity. 
      apply H2.
      * apply bs.
      * assumption.
      * assumption.
      * apply H4.
        assumption.
    + inversion X0. subst. 
      eapply T_Let.
      * reflexivity.
      * unfold P_bindings_rec in H2. edestruct H2 as [_ [Heq _]]. apply Heq in X1. rewrite <- X1. assumption.
      * apply H2. assumption. assumption.
      * unfold P_bindings_rec in H2. edestruct H2 as [_ [Heq _]]. apply Heq in X1. rewrite <- X1. apply H4. assumption. 
  - (* T_LetRec *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    eapply T_LetRec.
    + reflexivity.
    + unfold P_bindings_rec in H2.
      edestruct H2 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      assumption.
    + unfold P_bindings_rec in H2.
      edestruct H2 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply IHH. auto. auto.
    + unfold P_bindings_rec in H2.
      edestruct H2 as [IHH Heq].
      apply Heq in X1 as Hsu.
      rewrite <- Hsu.
      apply H4.
      assumption.
  - (* T_Var *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Var. assumption.
  - (* T_TyAbs *)
    intros. unfold P_term. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyAbs.
    unfold P_term in H0.
    apply H0.
    apply X2.
  - (* T_LamAbs *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_LamAbs.
    + apply H0. assumption.
    + assumption.
  - (* T_Apply *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Apply with T1.
    + apply H0. assumption.
    + apply H2. assumption.
  - (* T_Constant *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Constant.
  - (* T_Builtin *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Builtin.
  - (* T_TyInst *)
    intros. unfold P_term. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyInst with (T1 := T1) (X := X) (K2 := K2).
    + apply H0. assumption.
    + assumption.
    + assumption.
  - (* T_Error *)
    intros. unfold P_term. intros.
    inversion X. subst.
    inversion X0. subst.
    apply T_Error.
    apply H.
  - (* T_IWrap *)
    intros. unfold P_term. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_IWrap with (X := X) (K := K) (S := S).
    + assumption.
    + apply H1. assumption.
    + assumption.
    + assumption.
  - (* T_Unwrap *)
    intros. unfold P_term. intros.
    inversion X0. subst.
    inversion X1. subst.
    apply T_Unwrap with (F := F) (X := X) (K := K) (T := T).
    + apply H0. assumption.
    + assumption.
    + assumption.

  - (* W_Con *)
    intros. unfold P_constructor. intros.
    apply W_Con. assumption.

  - (* W_NilB_NonRec *)
    intros. unfold P_bindings_nonrec. intros.
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
        assumption.
  - (* W_ConsB_NonRec *)
    intros. unfold P_bindings_nonrec. intros.
    split.
    + intros.
      inversion X. subst.
      apply W_ConsB_NonRec.
      * apply H0. assumption. assumption.
      * unfold P_binding in H0.
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
        replace ctx with ([] ++ ctx) by reflexivity. 
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
              rewrite concat_app in H4.
              simpl in H4.
              rewrite <- app_assoc in H4.
              simpl in H4.
              apply H4.
    
  - (* W_NilB_Rec *)
    intros. unfold P_bindings_rec. intros.
    split.
    + intros.
      inversion X. subst.
      assumption.
    + intros.
      inversion X. subst.
      reflexivity.
  - (* W_ConsB_Rec*)
    intros. unfold P_bindings_rec. intros.
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
    intros. unfold P_binding. intros.
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
          ++ assumption. 
          ++ assumption.
        -- apply H1. assumption.
  - (* W_Type *)
    intros. unfold P_binding. intros.
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
    intros. unfold P_binding. intros.
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

End Named.