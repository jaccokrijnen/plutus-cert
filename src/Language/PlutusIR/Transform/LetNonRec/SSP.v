Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Definition P_has_type Delta Gamma t1 T : Prop := 
  forall t2, 
    CNR_Term t1 t2 -> 
    Delta ,, Gamma |-+ t2 : T.

Definition P_constructor_well_formed Delta c T : Prop := 
  Delta |-ok_c c : T.

Definition P_bindings_well_formed_nonrec Delta Gamma bs1 : Prop :=
  (
    forall bs2,
      Delta ,, Gamma |-oks_nr bs1 ->
      Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
      Delta ,, Gamma |-oks_nr bs2 /\
      map binds_Delta bs2 = map binds_Delta bs1 /\
      map binds_Gamma bs2 = map binds_Gamma bs1
  ) /\ (
    forall f_bs2 t T bs1Gn,
      Delta ,, Gamma |-oks_nr bs1 -> 
      CNR_Bindings bs1 f_bs2 ->
      map_normalise (flatten (map binds_Gamma bs1)) bs1Gn ->
      (mupdate Delta (flatten (map binds_Delta bs1))) ,, (mupdate Gamma bs1Gn) |-+ t : T ->
      Delta ,, Gamma |-+ (fold_right apply t f_bs2) : T
  ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop :=
  forall bs2,
    Delta ,, Gamma |-oks_r bs1 ->
    Congruence.Cong_Bindings CNR_Term bs1 bs2 ->
    Delta ,, Gamma |-oks_r bs2 /\
    map binds_Delta bs2 = map binds_Delta bs1 /\
    map binds_Gamma bs2 = map binds_Gamma bs1.

Definition P_binding_well_formed Delta Gamma b1 : Prop := 
  (
    forall b2,
      Delta ,, Gamma |-ok_b b1 ->
      Congruence.Cong_Binding CNR_Term b1 b2 ->
      Delta ,, Gamma |-ok_b b2 /\
      binds_Delta b2 = binds_Delta b1 /\
      binds_Gamma b2 = binds_Gamma b1
  ) /\ (
    forall f_b2 t T bs1Gn,
      Delta ,, Gamma |-ok_b b1 ->
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
      unfold P_bindings_well_formed_nonrec in H3.
      destruct H3 as [[IHH [Heq Heq']] _]...
      eapply T_Let...
      * rewrite Heq'...
      * rewrite Heq...
  - (* T_LetRec *)
    inversion X. subst.
    inversion X0. subst.
    unfold P_bindings_well_formed_rec in H3.
    edestruct H3 as [IHH [Heq Heq']]...
    eapply T_LetRec...
    + rewrite Heq'...
    + rewrite Heq...
    + rewrite Heq...
    
  - (* W_NilB_NonRec *)
    split. all: intros.
    + inversion X... 
    + inversion X.
      inversion H0.
      subst...
  - (* W_ConsB_NonRec *)
    split. all: intros.
    + inversion X. subst.
      unfold P_binding_well_formed in H0.
      destruct H0 as [[IH [Heq Heq']] _]...
      split; try split.
      * eapply W_ConsB_NonRec...
        -- rewrite Heq'...
        -- rewrite Heq... eapply H3...
      * simpl. rewrite Heq...
        f_equal. eapply H3...
      * simpl. rewrite Heq'...
        f_equal. eapply H3...
    + inversion X. subst.
      inversion X0. subst.
      destruct H0 as [_ IH1]...
      destruct H3 as [_ IH2]...
      simpl.

      simpl in H5.
      unfold flatten in H5.
      simpl in H5.
      rewrite concat_app in H5.
      simpl in H5.
      apply map_normalise__app in H5 as H7.
      destruct H7 as [l1n [l2n [Hn__l1n [H1__l2n Heql]]]].
      simpl in H1__l2n.
      inversion H1__l2n. subst.
      inversion H9. subst.

      simpl in H1.
      inversion H1. subst.
      inversion H11. subst.

      eapply normalisation__deterministic in H10...
      subst.

      eapply IH1...
      eapply IH2...

      simpl in H6.
      rewrite mupdate_app in H6.
      unfold flatten in H6.
      simpl in H6.
      rewrite concat_app in H6.
      simpl in H6.
      rewrite app_nil_r in H6.

      eapply H6.

  - (* W_NilB_Rec *)
    inversion X. subst.
    eauto.
  - (* W_ConsB_Rec*)
    inversion X. subst.
    unfold P_binding_well_formed in H0.
    destruct H0 as [[IH [Heq Heq']] _]...
    split; try split.
    + eapply W_ConsB_Rec...
      eapply H2...
    + simpl. rewrite Heq...
      f_equal. eapply H2...
    + simpl. rewrite Heq'...
      f_equal. eapply H2...
           
  - (* W_Term *)
    split. all: intros.
    + inversion X. subst...
    + inversion X. subst...
      simpl in H4.
      inversion H4. subst.
      inversion H10. subst.
      eapply normalisation__deterministic in H0...
      subst...
  - (* W_Type *)
    split. all: intros.
    + inversion X0. subst...
    + inversion X0.
  - (* W_Data *)
    split. all: intros.
    + inversion X0. subst...
    + inversion X0.
Qed. 
