Require Import PlutusCert.PlutusIR.

Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.

Require Import Coq.Lists.List.

(** Term variable bindings *)

Lemma In_bvc_constrBind : forall cs x d,
    In x (map bvc cs) ->
    In x (map fst (map (constrBind d) cs)).
Proof with eauto.
  induction cs. all: intros.
  - simpl in H. simpl...
  - destruct a as [y T].
    destruct d.
    simpl in H.
    destruct H.
    all: simpl...
Qed.

Lemma notIn_bvc_constrBind : forall cs x d,
    ~ In x (map bvc cs) ->
    ~ In x (map fst (map (constrBind d) cs)).
Proof with eauto.
  induction cs. all: intros.
  - simpl in H. simpl...
  - destruct a as [y T].
    destruct d.
    simpl in H.
    intros Hcon.
    simpl in Hcon.
    destruct Hcon...
    eapply IHcs...
Qed.

Lemma In_bvb_bindsG: forall x b,
    In x (bvb b) ->
    In x (map fst (binds_Gamma b)).
Proof with eauto.
  intros.
  destruct b.
  all: simpl in H.
  - destruct v.
    simpl in H.
    simpl...
  - destruct t.
    simpl in H.
    simpl...
  - destruct d.
    destruct t.
    simpl in H.
    simpl.
    destruct H.
    + subst...
    + right...
      apply in_rev in H.
      rewrite map_rev.
      apply -> in_rev.
      eapply In_bvc_constrBind...
Qed.

Lemma notIn_bvb_bindsG : forall x b,
    ~ In x (bvb b) ->
    ~ In x (map fst (binds_Gamma b)).
Proof with eauto.
  intros.
  destruct b.
  all: simpl in H.
  - destruct v.
    simpl...
  - destruct t.
    simpl...
  - destruct d.
    destruct t.
    simpl...
    simpl in H...
    intros Hcon.
    apply Decidable.not_or in H.
    destruct H.
    destruct Hcon...
    rewrite <- In_rev in H0.
    eapply notIn_bvc_constrBind in H0.
    rewrite map_rev in H1.
    apply In_rev in H1.
    eapply H0...
Qed.

Lemma In_bvbs_bindsG : forall bs x,
    In x (bvbs bs) ->
    In x (map fst (flatten (map binds_Gamma bs))).
Proof with eauto.
  induction bs. all: intros.
  - simpl...
  - simpl.
    unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite map_app.
    apply in_or_app.
    unfold bvbs in H.
    simpl in H.
    apply in_app_or in H.
    destruct H...
    + right.
      rewrite app_nil_r.
      apply In_bvb_bindsG...
Qed.

Lemma notIn_bvbs_bindsG : forall bs x,
    ~ In x (bvbs bs) ->
    ~ In x (map fst (flatten (map binds_Gamma bs))).
Proof with eauto.
  induction bs. all: intros.
  - simpl...
  - simpl.
    unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite map_app.
    rewrite app_nil_r.
    rewrite in_app_iff.
    simpl in H.
    unfold bvbs in H.
    simpl in H.
    rewrite in_app_iff in H.
    apply Decidable.not_or in H.
    destruct H.
    intros Hcon.
    destruct Hcon...
    + eapply IHbs...
    + eapply notIn_bvb_bindsG...
Qed.

Lemma In__map_normalise : forall l x ln,
    In x (map fst l) ->
    map_normalise l ln ->
    In x (map fst ln).
Proof with eauto.
  induction l. all: intros.
  - simpl in H. exfalso...
  - inversion H0. subst.
    destruct H. all: subst.
    + simpl...
    + simpl...
Qed.

Lemma notIn__map_normalise : forall l x ln,
    ~ In x (map fst l) ->
    map_normalise l ln ->
    ~ In x (map fst ln).
Proof with eauto.
  induction l. all: intros.
  - inversion H0. subst...
  - inversion H0. subst.
    simpl in H.
    apply Decidable.not_or in H.
    destruct H.
    intros Hcon.
    destruct Hcon...
    eapply IHl...
Qed.



(** Type variable bindings *)

Lemma In_btvb_bindsD: forall x b,
    In x (btvb b) ->
    In x (map fst (binds_Delta b)).
Proof with eauto.
  intros.
  destruct b.
  all: simpl in H.
  - destruct v...
  - destruct t...
  - destruct d.
    destruct t...
Qed.

Lemma notIn_btvb_bindsD : forall x b,
    ~ In x (btvb b) ->
    ~ In x (map fst (binds_Delta b)).
Proof with eauto.
  intros.
  destruct b.
  all: simpl in H.
  - destruct v...
  - destruct t...
  - destruct d.
    destruct t...
Qed.

Lemma In_btvbs_bindsD : forall bs x,
    In x (btvbs bs) ->
    In x (map fst (flatten (map binds_Delta bs))).
Proof with eauto.
  induction bs. all: intros.
  - simpl...
  - unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite map_app.
    apply in_or_app.
    unfold btvbs in H.
    simpl in H.
    apply in_app_or in H.
    destruct H...
    + right.
      rewrite app_nil_r.
      apply In_btvb_bindsD...
Qed.

Lemma notIn_btvbs_bindsD : forall bs x,
    ~ In x (btvbs bs) ->
    ~ In x (map fst (flatten (map binds_Delta bs))).
Proof with eauto.
  induction bs. all: intros.
  - simpl...
  - simpl.
    unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite map_app.
    rewrite app_nil_r.
    rewrite in_app_iff.
    simpl in H.
    unfold btvbs in H.
    simpl in H.
    rewrite in_app_iff in H.
    apply Decidable.not_or in H.
    destruct H.
    intros Hcon.
    destruct Hcon...
    + eapply IHbs...
    + eapply notIn_btvb_bindsD...
Qed.
