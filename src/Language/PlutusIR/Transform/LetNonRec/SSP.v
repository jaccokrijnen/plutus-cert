Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Definition P_has_type Delta Gamma t1 T := 
  forall t2, 
    CNR_Term t1 t2 -> 
    Delta ,, Gamma |-+ t2 : T.

Definition P_constructor_well_formed Delta c := Delta |-ok_c c.

Definition P_bindings_well_formed_nonrec Delta Gamma bs1 :=
    forall bs2, (
      Delta ,, Gamma |-oks_nr bs1 ->
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      Delta ,, Gamma |-oks_nr bs2
    ) /\ (
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      map binds_Delta bs1 = map binds_Delta bs2 /\
      map binds_Gamma bs1 = map binds_Gamma bs2
    ) /\ (
      forall f_bs2 t T bs1Gn,
        Delta ,, Gamma |-oks_nr bs1 -> 
        CNR_Bindings bs1 f_bs2 ->
        map_normalise (flatten (map binds_Gamma bs1)) bs1Gn ->
        (mupdate Delta (flatten (map binds_Delta bs1))) ,, (mupdate Gamma bs1Gn) |-+ t : T ->
        Delta ,, Gamma |-+ (fold_right apply t f_bs2) : T
    ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 :=
  forall bs2, (
    Delta ,, Gamma |-oks_r bs1 ->
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    Delta ,, Gamma |-oks_r bs2
  ) /\ (
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    map binds_Delta bs1 = map binds_Delta bs2 /\
    map binds_Gamma bs1 = map binds_Gamma bs2
  ).

Definition P_binding_well_formed Delta Gamma b1 := 
  forall b2, (
      Delta ,, Gamma |-ok b1 ->
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      Delta ,, Gamma |-ok b2
    ) /\ (
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      binds_Delta b1 = binds_Delta b2 /\
      binds_Gamma b1 = binds_Gamma b2
    ) /\ (
      forall f_b2 t T bs1Gn,
        Delta ,, Gamma |-ok b1 ->
        CNR_Binding b1 f_b2 ->
        map_normalise (binds_Gamma b1) bs1Gn ->
        mupdate Delta (binds_Delta b1) ,, mupdate Gamma bs1Gn |-+ t : T ->
        Delta ,, Gamma |-+ (f_b2 t) : T  
    ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed
  : core.

Theorem CNR_Term__SSP : forall Delta Gamma t1 T,
    Delta ,, Gamma |-+ t1 : T ->
    P_has_type Delta Gamma t1 T.
Proof.
  apply has_type__ind with 
    (P := P_has_type) 
    (P0 := P_constructor_well_formed) 
    (P1 := P_bindings_well_formed_nonrec) 
    (P2 := P_bindings_well_formed_rec) 
    (P3 := P_binding_well_formed).
  all: intros; autounfold; intros.
  - (* T_Let *)
    inversion X; subst.
    + eapply H3.
      * apply bs.
      * assumption.
      * assumption.
      * eassumption.
      * apply H5.
        assumption.
    + inversion X0. subst. 
      eapply T_Let.
      * reflexivity.
      * unfold P_bindings_well_formed_nonrec in H3.
        edestruct H3 as [_ [Heq _]].
        apply Heq in X1.
        destruct X1.
        rewrite <- H1.
        eassumption.
      * reflexivity.
      * apply H3. assumption. assumption.
      * unfold P_bindings_well_formed_nonrec in H3. edestruct H3 as [_ [Heq _]]. apply Heq in X1. 
        destruct X1. rewrite <- H. apply H5. assumption. 
  - (* T_LetRec *)
    inversion X. subst.
    inversion X0. subst.
    eapply T_LetRec.
    + reflexivity.
    + unfold P_bindings_well_formed_rec in H3.
      edestruct H3 as [IHH Heq].
      apply Heq in X1 as Hsu.
      destruct Hsu.
      rewrite <- H1.
      eassumption.
    + reflexivity.
    + unfold P_bindings_well_formed_rec in H3.
      edestruct H3 as [IHH Heq].
      apply Heq in X1 as Hsu.
      destruct Hsu.
      rewrite <- H.
      apply IHH. auto. auto.
    + unfold P_bindings_well_formed_rec in H3.
      edestruct H3 as [IHH Heq].
      apply Heq in X1 as Hsu.
      destruct Hsu.
      rewrite <- H.
      apply H5.
      assumption.
  - (* T_Var *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Var with T. 
    assumption.
    assumption.
  - (* T_TyAbs *)
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyAbs.
    unfold P_has_type in H0.
    apply H0.
    apply X2.
  - (* T_LamAbs *)
    inversion X. subst.
    inversion X0. subst.
    apply T_LamAbs.
    + assumption.
    + assumption.
    + apply H2. assumption.
  - (* T_Apply *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Apply with T1n.
    + apply H0. assumption.
    + apply H2. assumption.
  - (* T_Constant *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Constant.
  - (* T_Builtin *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Builtin.
    reflexivity.
  - (* T_TyInst *)
    inversion X0. subst.
    inversion X1. subst.
    apply T_TyInst with T1n X K2 T2n.
    + apply H0. assumption.
    + assumption.
    + assumption.
    + assumption.
  - (* T_Error *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Error.
    assumption.
    assumption.
  - (* T_IWrap *)
    inversion X. subst.
    inversion X0. subst.
    apply T_IWrap with K T0n.
    + assumption.
    + apply H1. assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - (* T_Unwrap *)
    inversion X. subst.
    inversion X0. subst.
    apply T_Unwrap with Fn K Tn.
    + apply H0. assumption.
    + assumption.
    + assumption.
    
  - (* T_ExtBuiltin *)
    inversion X. subst.
    inversion X0.
    
  - (* W_Con *)
    eapply W_Con; eauto.
    
  - (* W_NilB_NonRec *)
    split.
    + intros.
      inversion X. subst.
      assumption.
    + split.
      * intros.
        inversion X. subst.
        auto.
      * intros.
        inversion X. subst.
        simpl in H0.
        inversion H0. subst.
        assumption.
  - (* W_ConsB_NonRec *)
    split.
    + intros.
      inversion X. subst.
      eapply W_ConsB_NonRec.
      * apply H0. assumption. assumption.
      * unfold P_binding_well_formed in H0.
        edestruct H0 as [_ [Heq _]].
        apply Heq in X0.
        destruct X0.
        rewrite <- H6.
        eassumption.
      * unfold P_binding_well_formed in H0.
        edestruct H0 as [_ [Heq _]].
        apply Heq in X0.
        destruct X0.
        rewrite <- H5.
        apply H3. assumption. assumption.
    + split.
      * intros.
        inversion X. subst.
        simpl.
        split.
        -- f_equal.
           ++ apply H0. assumption.
           ++ apply H3. assumption.
        -- f_equal.
           ++ apply H0. assumption.
           ++ apply H3. assumption.
      * intros.
        inversion X. subst.
        inversion X0. subst.
        edestruct H3 as [_ [_ J]].
        
        simpl.
        edestruct H0 as [_ [_ J2]].
        eapply J2.
        -- assumption.
        -- assumption.
        -- eassumption.
        -- unfold flatten in H5.
            simpl in H5.
            rewrite concat_app in H5.
            simpl in H5.
            apply map_normalise__app in H5 as H20. 
            destruct H20 as [l1n [l2n [Hmn1 [Hmn2 Heq]]]].
            subst. 

          eapply J.
           ++ assumption.
           ++ assumption.
           ++ eauto.
           ++ simpl.
              simpl in H6.
              unfold flatten in H6.
              simpl in H6.  
              rewrite concat_app in H6.
              simpl in H6.
              rewrite app_nil_r in H6.
              rewrite mupdate_app in H6.
              simpl in H6.
              simpl in H1.
              eapply map_normalise__deterministic in H1; eauto.
              subst.
              apply H6.
  - (* W_NilB_Rec *)
    split.
    + intros.
      inversion X. subst.
      assumption.
    + intros.
      inversion X. subst.
      auto.
  - (* W_ConsB_Rec*)
    split.
    + intros.
      inversion X. subst.
      apply W_ConsB_Rec.
      * apply H0. assumption. assumption.
      * apply H2. assumption. assumption.
    + intros.
      inversion X. subst.
      simpl.
      split.
      -- f_equal.
         ++ apply H0. assumption.
         ++ apply H2. assumption.
      -- f_equal.
         ++ apply H0. assumption.
         ++ apply H2. assumption.
           
  - (* W_Term *)
    split.
    + intros. 
      inversion X. subst.
      apply W_Term.
      * assumption.
      * apply H1. assumption.
    + split. 
      * intros.
        inversion X. subst.
        auto.
      * intros.
        inversion X. subst.
        apply strong_normalisation in H as He.
        destruct He.
        eapply T_Apply.
        -- apply T_LamAbs.
          ++ simpl in H3.
             assumption. 
          ++ apply H5.
          ++ simpl in H4.
             simpl in H3.
             inversion H3. subst.
             inversion H10. subst.
             eapply normalise_deterministic in H5; eauto.
             subst.
             simpl in H4.
            eassumption.
        -- apply has_type__normal in H0 as H10.
           eapply normalisation__stability in H10; eauto.
           subst. eapply H1. assumption.
  - (* W_Type *)
    split.
    + intros. 
      inversion X0. subst.
      apply W_Type.
      assumption.
    + split.
      * intros.
        inversion X0. subst.
        auto.
      * intros.
        inversion X0.
  - (* W_Data *)
    split.
    + intros.
      inversion X0. subst.
      assumption.
    + split.
      * intros.
        inversion X0. subst.
        auto.
      * intros.
        inversion X0.

  Unshelve. auto. apply (TermBind Strict (VarDecl v ty) t_bound).
Qed. 
