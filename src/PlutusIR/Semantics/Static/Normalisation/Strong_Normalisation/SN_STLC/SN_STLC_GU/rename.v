From PlutusCert Require Import STLC util Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Local Open Scope string_scope.

Lemma ren_lam_vacuous B x x' t s0 :
  rename x x' (@tmlam B x t s0) = @tmlam B x t s0.
Proof.
  unfold rename.
  simpl. rewrite String.eqb_refl. rewrite mren_id. reflexivity.
Qed.

Lemma ren_lam B x x' t s s0 :
  x <> s -> rename x x' (@tmlam B s t s0) = @tmlam B s t (rename x x' s0).
Proof.
  intros Hnotxs.
  unfold rename.
  simpl. rewrite <- String.eqb_neq in Hnotxs. rewrite Hnotxs.
  reflexivity.
Qed.

Lemma ren_commute x x' y y' s :
  x <> y ->
  x' <> y ->
  y' <> x ->
  rename x x' (rename y y' s) = rename y y' (rename x x' s).
Proof.
  intros Hxy Hx'y Hy'x.
  induction s.
  - simpl.
    destr_eqb_eq y s.
    + destr_eqb_eq x s.
      * contradiction.
      * unfold rename.
        simpl. rewrite String.eqb_refl. rewrite <- String.eqb_neq in H. rewrite H. simpl.
        rewrite <- String.eqb_neq in Hy'x. rewrite String.eqb_sym in Hy'x. rewrite Hy'x.
        rewrite String.eqb_refl.
        reflexivity.
    + unfold rename. simpl. rewrite <- String.eqb_neq in H. rewrite H.
      destr_eqb_eq x s.
      * simpl. rewrite String.eqb_refl. rewrite <- String.eqb_neq in Hx'y. rewrite String.eqb_sym in Hx'y. rewrite Hx'y.
        reflexivity.
      * simpl. rewrite <- String.eqb_neq in H0. rewrite H0. rewrite H.
        reflexivity.   
  - destr_eqb_eq y s.
    + rewrite ren_lam_vacuous.
      rewrite ren_lam; [|assumption].
      rewrite ren_lam_vacuous.
      reflexivity.
    + destr_eqb_eq x s.
      * rewrite ren_lam_vacuous;
        rewrite ren_lam; [|assumption].
        rewrite ren_lam_vacuous; reflexivity.
      * rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite ren_lam; [|assumption].
        rewrite IHs.
        reflexivity.
  - unfold rename. simpl.
    unfold rename in IHs1.
    unfold rename in IHs2.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - constructor.
Qed.

Lemma ren_two_vacuous {x Y' Y s }:
  x <> Y ->
  rename x Y' (rename x Y s) = rename x Y s.
Proof.

Admitted.

Lemma ren_vacuous X Y s :
  ~ In X (ftv s) -> rename X Y s = s.
Proof.
  intros HXnotIns.
  induction s.
  - unfold ftv in HXnotIns.
    apply not_in_cons in HXnotIns.
    unfold rename. unfold mren. simpl.
    destruct HXnotIns as [HXnots _].
    rewrite <- String.eqb_neq in HXnots.
    rewrite HXnots.
    reflexivity.
  - destr_eqb_eq X s.
    + rewrite ren_lam_vacuous.
      reflexivity.
    + rewrite ren_lam; auto.
      rewrite IHs.
      reflexivity.
      intros HContra.
      contradiction HXnotIns.
      unfold ftv. fold ftv.
      apply Util.List.in_remove. split; auto.
  - unfold rename. unfold mren. fold mren. simpl.
    unfold ftv in HXnotIns. fold ftv in HXnotIns.
    apply not_in_app in HXnotIns as [HXnotIns1 HXnotIns2].
    specialize (IHs1 HXnotIns1).
    specialize (IHs2 HXnotIns2).
    unfold rename in IHs1.
    unfold rename in IHs2.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - constructor.
Qed.