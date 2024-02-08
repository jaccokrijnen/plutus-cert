Require Import PlutusCert.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.PlutusIR.Transform.LetNonRec.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.



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
      Compat.Compat_Bindings CNR_Term bs1 bs2 ->
      Delta ,, Gamma |-oks_nr bs2 /\
      map binds_Delta bs2 = map binds_Delta bs1 /\
      map binds_Gamma bs2 = map binds_Gamma bs1
  ) /\ (
    forall f_bs2 t T bs1Gn,
      Delta ,, Gamma |-oks_nr bs1 ->
      CNR_Bindings bs1 f_bs2 ->
      map_normalise (flatten (map binds_Gamma bs1)) bs1Gn ->
      (flatten (map binds_Delta bs1) ++ Delta ) ,, (bs1Gn ++ Gamma ) |-+ t : T ->
      Delta ,, Gamma |-+ (fold_right apply t f_bs2) : T
  ).

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop :=
  forall bs2,
    Delta ,, Gamma |-oks_r bs1 ->
    Compat.Compat_Bindings CNR_Term bs1 bs2 ->
    Delta ,, Gamma |-oks_r bs2 /\
    map binds_Delta bs2 = map binds_Delta bs1 /\
    map binds_Gamma bs2 = map binds_Gamma bs1.

Definition P_binding_well_formed Delta Gamma b1 : Prop :=
  (
    forall b2,
      Delta ,, Gamma |-ok_b b1 ->
      Compat.Compat_Binding CNR_Term b1 b2 ->
      Delta ,, Gamma |-ok_b b2 /\
      binds_Delta b2 = binds_Delta b1 /\
      binds_Gamma b2 = binds_Gamma b1
  ) /\ (
    forall f_b2 t T bs1Gn,
      Delta ,, Gamma |-ok_b b1 ->
      CNR_Binding b1 f_b2 ->
      map_normalise (binds_Gamma b1) bs1Gn ->
      binds_Delta b1 ++ Delta ,, bs1Gn ++ Gamma |-+ t : T ->
      Delta ,, Gamma |-+ (f_b2 t) : T
  ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed
  : core.

Ltac inv_CNR :=
  match goal with
  | H : CNR_Term _ _ |- _ => inversion H; subst
  | H : CNR_Bindings _ _ |- _ => inversion H; subst
  end.

Ltac inv_Compat :=
  match goal with
    | H : Compat.Compat _ _ _ |- _ => inversion H; subst
    | H : Compat.Compat_Bindings _ _ _ |- _ => inversion H; subst
    | H : Compat.Compat_Binding _ _ _ |- _ => inversion H; subst
  end.

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
  all: try solve [ inv_CNR; inv_Compat ; eauto with typing].

  - (* T_Builtin *)
    (* TODO: [wip/saturated-builtins] *)
    admit.
  - (* T_Let *)
    inv_CNR.
    + eapply H3...
    + inv_Compat.
      unfold P_bindings_well_formed_nonrec in H3.
      edestruct H3 as [[IHH [Heq Heq']] _]...
      eapply T_Let...
      * rewrite Heq'...
      * rewrite Heq...
  - (* T_LetRec *)
    inv_CNR.
    inv_Compat.
    unfold P_bindings_well_formed_rec in H3.
    edestruct H3 as [IHH [Heq Heq']]...
    eapply T_LetRec...
    + rewrite Heq'...
    + rewrite Heq...
    + rewrite Heq...

  - (* W_NilB_NonRec *)
    split. all: intros.
    + inv_Compat...
    + inv_CNR.
      inversion H1.
      subst...
  - (* W_ConsB_NonRec *)
    split. all: intros.
    + inv_Compat.
      unfold P_binding_well_formed in H0.
      edestruct H0 as [[IH [Heq Heq']] _]...
      split; try split.
      * eapply W_ConsB_NonRec...
        -- rewrite Heq'...
        -- rewrite Heq... eapply H3...
      * simpl. rewrite Heq...
        f_equal. eapply H3...
      * simpl. rewrite Heq'...
        f_equal. eapply H3...
    + inv_CNR.
      inversion H10. subst.
      destruct H0 as [_ IH1]...
      destruct H3 as [_ IH2]...
      simpl.

      simpl in H5.
      unfold flatten in H6.
      simpl in H6.
      rewrite concat_app in H6.
      simpl in H6.
      apply map_normalise__app in H6 as H9.
      destruct H9 as [l1n [l2n [Hn__l1n [Hn__l2n Heql]]]].
      simpl in Hn__l2n.
      inversion Hn__l2n. subst.
      inversion H13. subst.

      simpl in H1.
      inversion H1. subst.
      inversion H15. subst.

      eapply normalisation__deterministic in H14...
      subst.

      eapply IH1...
      eapply IH2...

      simpl in H6.
      rewrite <- app_assoc in H7.
      unfold flatten in H7.
      simpl in H7.
      rewrite concat_app in H7.
      simpl in H7.
      rewrite app_nil_r in H7.

      eapply H7.

  - (* W_NilB_Rec *)
    inv_Compat.
    eauto.
  - (* W_ConsB_Rec*)
    inv_Compat.
    unfold P_binding_well_formed in H0.
    edestruct H0 as [[IH [Heq Heq']] _]...
    split; try split.
    + eapply W_ConsB_Rec...
      eapply H2...
    + simpl. rewrite Heq...
      f_equal. eapply H2...
    + simpl. rewrite Heq'...
      f_equal. eapply H2...

  - (* W_Term *)
    split. all: intros.
    + inv_Compat...
    + inversion H4. subst...
      simpl in H5.
      inversion H5. subst.
      inversion H11. subst.
      eapply normalisation__deterministic in H0...
      subst...
  - (* W_Type *)
    split. all: intros.
    + inv_Compat...
    + inversion H1.
  - (* W_Data *)
    split. all: intros.
    + inv_Compat...
    + inversion H3.
Admitted.
