From PlutusCert Require Import STLC_named alpha util rename step alpha_ctx_sub Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma fresh2_over_tv_term {Y t sigma} :
  Y = fresh2 sigma t ->
  ~ In Y (tv t).
Proof.
  intros Hfresh.
  intros Hcontra.
  unfold fresh2 in Hfresh.
Admitted.

Lemma fresh2_over_key_sigma X s t Y sigma :
  Y = fresh2 sigma t ->
  In (X, s) sigma -> Y <> X.
Admitted.

Lemma fresh2_over_tv_value_sigma X s t Y sigma :
  Y = fresh2 sigma t ->
  In (X, s) sigma -> ~ In Y (tv s).
Admitted.

Lemma alpha_not_in_tv_helper {X X' ren t} :
  ~ In X (tv t) -> ~ In X' (tv t) -> Alpha ren t t -> Alpha ((X, X')::ren) t t.
Proof.
Admitted.

Lemma alpha_not_in_ftv_helper2 {X X' ren t t'} :
  ~ In X (ftv t) -> Alpha ((X, X')::ren) t t' -> ~ In X' (ftv t') .
Admitted.

Lemma alpha_in_ftv_helper2 {X X' ren t t'} :
  In X (ftv t) -> Alpha ((X, X')::ren) t t' -> In X' (ftv t') .
Admitted.

Lemma weaken_vacuous_alpha {X X' ren t t'} :
  Alpha ((X, X')::ren) t t' -> ~ In X (ftv t) -> ~ In X' (ftv t') -> Alpha ren t t'.
Proof.
  (* Proof will go something similar to alphaRenameStronger *)
Admitted.

Lemma ftv_var x x' :
  In x (ftv (tmvar x')) -> x = x'.
Proof.
  simpl. intuition.
Qed.

Lemma not_in_ftv_var x x' :
  ~ In x (ftv (tmvar x')) -> x <> x'.
Proof.
  simpl. intuition.
Qed.

Lemma ftv_var_eq x :
  In x (ftv (tmvar x)).
Proof.
  simpl. intuition.
Qed.

Lemma not_ftv_app_not_left t1 t2 x :
  ~ In x (ftv (tmapp t1 t2)) -> ~ In x (ftv t1).
Proof.
Admitted.

Lemma not_ftv_app_not_right t1 t2 x :
  ~ In x (ftv (tmapp t1 t2)) -> ~ In x (ftv t2).
  Proof.
  Admitted.

(* By X in ftv tmlam Y, we know X <> Y.
  It doesnt matter wheteher Y' = X, if it is, then also X in ftv (rename Y Y' t).
*)
Lemma ftv_lam_rename_helper X Y Y' A t :
   In X (ftv (tmlam Y A t)) -> In X (ftv (rename Y Y' t)).
Admitted.

(* We don't need the X <> Y condition, because if X = Y, 
the lhs is non-sensical and always false *)
Lemma ftv_lam_helper X Y A t :
   In X (ftv (tmlam Y A t)) -> In X (ftv t).
Proof.
  (* intros HXnotY. *)
  intros Hftvlam.
  unfold ftv in Hftvlam.
  fold ftv in Hftvlam.
  apply in_remove in Hftvlam as [Hftvlam Hftvlam2].
  assumption.
Qed.

Lemma ftv_lam_negative X Y A t :
  ~ In X (ftv (tmlam Y A t)) -> X <> Y -> ~ In X (ftv t).
Admitted.

Lemma tv_not_lam X Y A t :
  ~ In X (tv (tmlam Y A t)) -> prod (X <> Y) (~ In X (tv t)).
Proof.
  intros HXnotinlam.
  unfold tv in HXnotinlam.
  fold tv in HXnotinlam.
  split; now apply not_in_cons in HXnotinlam.
Qed.


Lemma tv_not_app_l X Y A t :
  ~ In X (tv (tmlam Y A t)) -> prod (X <> Y) (~ In X (tv t)).
Proof.
Admitted.

Lemma tv_lam_rename_helper X Y Y' A t :
   Y <> Y' -> ~ In X (tv (tmlam Y A t)) -> ~ In X (tv (rename Y Y' t)).
Admitted.

Lemma ftv_lam_in_no_binder Y X A t :
  In Y (ftv (tmlam X A t)) -> X <> Y.
Proof.
Admitted.

Lemma ftv_lam_no_binder X A t :
  ~ In X (ftv (tmlam X A t)).
Proof.
  unfold ftv.
  fold ftv.
  intros HContra.
  apply in_remove in HContra as [_ HContra].
  contradiction.
Qed.

Lemma extend_ftv_to_tv x s :
  In x (ftv s) -> In x (tv s).
Proof.
Admitted.

Lemma tv_rename_vacuous_helper {X Y Y' t} :
  X <> Y -> In X (tv t) -> In X (tv (rename Y Y' t)).
Proof.
  intros HXnotY.
  intros HXtvt.
  induction t.
  - unfold tv in HXtvt.
    apply in_inv in HXtvt as [Hxs | HXinempty]; try contradiction.
    subst.
    unfold rename. unfold mren. simpl.
    rewrite <- String.eqb_neq in HXnotY. rewrite String.eqb_sym in HXnotY. rewrite HXnotY.
    unfold tv.
    apply in_eq.
  - destr_eqb_eq X s.
    + rewrite ren_lam; auto.
      unfold tv. fold tv.
      apply in_eq.
    + destr_eqb_eq Y s.
      * rewrite ren_lam_vacuous.
        unfold tv. fold tv.
        apply in_cons.
        unfold tv in HXtvt. fold tv in HXtvt.
        apply in_inv in HXtvt.
        destruct HXtvt; auto.
        symmetry in H0.
        contradiction.
      * rewrite ren_lam; auto.
        assert (In X (tv t0)).
        {
          unfold tv in HXtvt. fold tv in HXtvt.
          apply in_inv in HXtvt; auto.
          destruct HXtvt; auto.
          symmetry in H1.
          contradiction.
        }
        unfold tv. fold tv.
        apply in_cons.
        now apply IHt.
  - unfold rename. unfold mren. fold mren. simpl.
    unfold tv in HXtvt. fold tv in HXtvt.
    apply in_app_or in HXtvt.
    destruct HXtvt.
    + specialize (IHt1 H).
      unfold tv. fold tv.
      apply in_or_app. left. apply IHt1.
    + specialize (IHt2 H).
      unfold tv. fold tv.
      apply in_or_app. right. apply IHt2.
Qed.

Lemma tv_not_after_rename x y z s :
  z <> y -> ~ In z (tv s) -> ~ In z (tv (rename x y s)).
Proof.
Admitted.



Lemma ftv_rename_vacuous_helper {X Y Y' t} :
  X <> Y -> In X (ftv t) -> In X (ftv (rename Y Y' t)).
Proof.
  intros HXnotY.
  intros HXftvt.
  induction t.
  - assert (HXs: s = X).
    {
      unfold ftv in HXftvt. apply in_inv in HXftvt. destruct HXftvt; auto.
      contradiction.
    }
    subst.
    unfold rename. unfold mren. simpl. rewrite <- String.eqb_neq in HXnotY.
    rewrite <- String.eqb_sym in HXnotY. rewrite HXnotY.
    unfold ftv.
    auto.
  - assert (HXnots: s <> X).
    {
      intros HContra.
      subst.
      apply ftv_lam_no_binder in HXftvt.
      contradiction.
    }
    assert (Xftvt0: In X (ftv t0)).
    {
      unfold ftv in HXftvt. fold ftv in HXftvt.
      apply in_remove in HXftvt as [HXftvt0 HXftvt].
      assumption.
    }
    specialize (IHt Xftvt0).
    destr_eqb_eq Y s.
    + rewrite ren_lam_vacuous. assumption.
    + rewrite ren_lam; auto.
      unfold ftv. fold ftv.
      apply Util.List.in_remove; auto.
  - unfold rename. unfold mren. fold mren. simpl.
    unfold ftv in HXftvt. fold ftv in HXftvt.
    apply in_app_or in HXftvt.
    destruct HXftvt.
    + specialize (IHt1 H).
      apply in_or_app. left. apply IHt1.
    + specialize (IHt2 H).
      apply in_or_app. right. apply IHt2.
Qed.

Lemma ftv_not_in_rename X Y Y' t:
  X <> Y' -> ~ In X (ftv t) -> ~ In X (ftv (rename Y Y' t)).
Admitted.

Lemma ftv_not_in_after_rename Y Y' t:
  Y <> Y' -> ~ In Y (ftv (rename Y Y' t)).
Admitted.

(* If there is a free X in t, then renaming replaces this by Y.

This Y is now in t, but it could be capture by a binder that coincidentally is Y

Luckily we only need to knnow Y in the tv (not necessarily Y in the ftv)*)
Lemma ftv_tv_rename_helper X Y t :
  In X (ftv t) -> In Y (tv (rename X Y t)).
Proof.
  intros HXftvt.
  induction t.
  - unfold ftv in HXftvt.
    apply in_inv in HXftvt as [Hxs | HXinempty]; try contradiction.
    subst.
    unfold rename. unfold mren. simpl.
    rewrite String.eqb_refl.
    unfold ftv.
    apply in_eq.
  - assert (X <> s).
    {
      intros HContra.
      subst.
      apply ftv_lam_no_binder in HXftvt.
      contradiction.
    }
    rewrite ren_lam; auto.

    apply ftv_lam_helper in HXftvt.
    specialize (IHt HXftvt).

    unfold tv. fold tv.
    apply in_cons.
    assumption.
  - unfold ftv in HXftvt. fold ftv in HXftvt.
    apply in_app_or in HXftvt.
    destruct HXftvt.
    + specialize (IHt1 H).
      unfold tv. fold tv.
      apply in_or_app. left. apply IHt1.
    + specialize (IHt2 H).
      unfold tv. fold tv.
      apply in_or_app. right. apply IHt2.
Qed.

Lemma alpha_extend_fresh {x x' ren t t'}:
  ~ In x (ftv t) ->
  ~ In x' (ftv t') ->
  Alpha ren t t' ->
  Alpha ((x, x')::ren) t t'.
Proof.
Admitted.

(* Idk, but must be true. *)
Lemma tv_keys_env_helper y s sigma sigma_:
  y = fresh2 (sigma_ ++ sigma) s ->
  ~ In y (tv_keys_env sigma).
Proof.
Admitted.

Lemma not_env_not_val y sigma t :
  In t (map snd sigma) -> ~ In y (tv_keys_env sigma) -> ~ In y (tv t).
Admitted.

Lemma in_tv_value_then_in_tv_keys_env y y1 t (sigma : list (string * term)) :
  In y (tv t) -> In (y1, t) sigma -> In y (tv_keys_env sigma).
Proof.
Admitted.

Lemma btv_lam {X A t} :
  In X (btv (tmlam X A t)).
Proof.
  unfold btv.
  apply in_eq.
Qed.