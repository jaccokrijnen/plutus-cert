Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Definition P_has_type flag Delta Gamma t1 T := 
  forall t2, 
    CNR_Term t1 t2 -> 
    Delta ,, Gamma ;; flag |-+ t2 : T.

Definition P_constructor_well_formed Delta c T := Delta |-ok_c c : T.

Definition P_bindings_well_formed_nonrec flag Delta Gamma bs1 :=
    forall bs2, (
      Delta ,, Gamma ;; flag |-oks_nr bs1 ->
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      Delta ,, Gamma ;; flag |-oks_nr bs2
    ) /\ (
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      map binds_Delta bs1 = map binds_Delta bs2 /\
      map binds_Gamma bs1 = map binds_Gamma bs2
    ) /\ (
      forall f_bs2 t T bs1Gn,
        Delta ,, Gamma ;; flag |-oks_nr bs1 -> 
        CNR_Bindings bs1 f_bs2 ->
        map_normalise (flatten (map binds_Gamma bs1)) bs1Gn ->
        (mupdate Delta (flatten (map binds_Delta bs1))) ,, (mupdate Gamma bs1Gn) ;; flag |-+ t : T ->
        Delta ,, Gamma ;; flag |-+ (fold_right apply t f_bs2) : T
    ).

Definition P_bindings_well_formed_rec flag Delta Gamma bs1 :=
  forall bs2, (
    Delta ,, Gamma ;; flag |-oks_r bs1 ->
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    Delta ,, Gamma ;; flag |-oks_r bs2
  ) /\ (
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    map binds_Delta bs1 = map binds_Delta bs2 /\
    map binds_Gamma bs1 = map binds_Gamma bs2
  ).

Definition P_binding_well_formed flag Delta Gamma b1 := 
  forall b2, (
      Delta ,, Gamma ;; flag |-ok_b b1 ->
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      Delta ,, Gamma ;; flag |-ok_b b2
    ) /\ (
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      binds_Delta b1 = binds_Delta b2 /\
      binds_Gamma b1 = binds_Gamma b2
    ) /\ (
      forall f_b2 t T bs1Gn,
        Delta ,, Gamma ;; flag |-ok_b b1 ->
        CNR_Binding b1 f_b2 ->
        map_normalise (binds_Gamma b1) bs1Gn ->
        mupdate Delta (binds_Delta b1) ,, mupdate Gamma bs1Gn ;; flag |-+ t : T ->
        Delta ,, Gamma ;; flag |-+ (f_b2 t) : T  
    ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed
  : core.

Theorem CNR_Term__SSP : forall flag Delta Gamma t1 T,
    Delta ,, Gamma ;; flag |-+ t1 : T ->
    P_has_type flag Delta Gamma t1 T.
Proof with (eauto with typing).
  apply has_type__ind with 
    (P := P_has_type) 
    (P0 := P_constructor_well_formed) 
    (P1 := P_bindings_well_formed_nonrec) 
    (P2 := P_bindings_well_formed_rec) 
    (P3 := P_binding_well_formed).
  all: intros; autounfold; intros.
  all: try solve [eauto with typing].
  all: try solve [inversion X; subst; inversion X0; subst; eauto with typing].
  all: try solve [inversion X0; subst; inversion X1; subst; eauto with typing].
  - (* T_Let *) 
    inversion X; subst.
    + eapply H3...
    + inversion X0; subst...
      eapply T_Let...
      * unfold P_bindings_well_formed_nonrec in H3.
        edestruct H3 as [_ [Heq _]].
        apply Heq in X1.
        destruct X1.
        rewrite <- H1.
        eassumption.
      * apply H3...
      * unfold P_bindings_well_formed_nonrec in H3. edestruct H3 as [_ [Heq _]]. apply Heq in X1. 
        destruct X1. rewrite <- H. apply H5. assumption. 
  - (* T_LetRec *)
    inversion X. subst.
    inversion X0. subst.
    eapply T_LetRec...
    + unfold P_bindings_well_formed_rec in H3.
      edestruct H3 as [IHH Heq].
      apply Heq in X1 as Hsu.
      destruct Hsu.
      rewrite <- H1.
      eassumption.
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
      eapply W_Term...
    + split. 
      * intros.
        inversion X. subst.
        auto.
      * intros.
        inversion X. subst.
        eapply T_Apply...
        -- apply T_LamAbs...
          ++ simpl in H4.
             inversion H4. subst.
             inversion H10. subst.
             eapply normalisation__deterministic in H0; eauto.
             subst.
             inversion H3. subst.
             simpl in H3.
             inversion H3. subst.
             inversion H10. subst.
             eassumption.
        -- apply has_type__normal in H1 as H10.
           unfold P_has_type in H2.
           destruct flag; eauto.
           eapply typing_subsumes_escaped_typing.
           eapply H2.
           eauto.
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
