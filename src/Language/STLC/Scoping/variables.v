(* Many small lemmas about
  - freshness of fresh2
  - ftv, tv, btv
    - with respect to renaming
  - ftv_keys_env, btv_env, tv_keys_env
  Admitted: All admits here are because of time constraints.
*)

From PlutusCert Require Import STLC util Util Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ren_lam_vacuous B x x' t s0 :
  rename x x' (@tmabs B x t s0) = @tmabs B x t s0.
Proof.
  unfold rename.
  simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma ren_lam B x x' t s s0 :
  x <> s -> rename x x' (@tmabs B s t s0) = @tmabs B s t (rename x x' s0).
Proof.
  intros Hnotxs.
  unfold rename.
  simpl. rewrite <- String.eqb_neq in Hnotxs. rewrite Hnotxs.
  reflexivity.
Qed.

(* Axiomatized freshness properties of the fresh2 procedure *)
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

Lemma ftv_var x x' :
  In x (ftv (tmvar x')) -> x = x'.
Proof.
  simpl. intuition.
Qed.

Lemma tv_var x x' :
  In x (tv (tmvar x')) -> x = x'.
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

Lemma not_ftv_app_not_left {B : BSort} t1 t2 x :
  ~ In x (ftv (@tmbin B t1 t2)) -> ~ In x (ftv t1).
Proof.
Admitted.

Lemma not_ftv_app_not_right {B : BSort} t1 t2 x :
  ~ In x (ftv (@tmbin B t1 t2)) -> ~ In x (ftv t2).
  Proof.
  Admitted.

(* By X in ftv tmabs Y, we know X <> Y.
  It doesnt matter wheteher Y' = X, if it is, then also X in ftv (rename Y Y' t).
*)
Lemma ftv_lam_rename_helper {B : USort} X Y Y' A t :
   In X (ftv (@tmabs B Y A t)) -> In X (ftv (rename Y Y' t)).
Admitted.

(* We don't need the X <> Y condition, because if X = Y, 
the lhs is non-sensical and always false *)
Lemma ftv_lam_helper {B : USort} X Y A t :
   In X (ftv (@tmabs B Y A t)) -> In X (ftv t).
Proof.
  intros Hftvlam.
  unfold ftv in Hftvlam.
  fold ftv in Hftvlam.
  apply in_remove in Hftvlam as [Hftvlam Hftvlam2].
  assumption.
Qed.

Lemma ftv_c_lam {B : USort} X Y A t :
  In X (ftv t) -> Y <> X -> In X (ftv (@tmabs B Y A t)).
Admitted.

Lemma ftv_lam_negative {B : USort} X Y A t :
  ~ In X (ftv (@tmabs B Y A t)) -> X <> Y -> ~ In X (ftv t).
Admitted.

Lemma tv_not_lam  {B : USort} X Y A t :
  ~ In X (tv (@tmabs B Y A t)) -> prod (X <> Y) (~ In X (tv t)).
Proof.
  intros HXnotinlam.
  unfold tv in HXnotinlam.
  fold tv in HXnotinlam.
  split; now apply not_in_cons in HXnotinlam.
Qed.


Lemma tv_not_app_l {B} X Y A t :
  ~ In X (tv (@tmabs B Y A t)) -> prod (X <> Y) (~ In X (tv t)).
Proof.
Admitted.

Lemma tv_lam_rename_helper {B} X Y Y' A t :
   Y <> Y' -> ~ In X (tv (@tmabs B Y A t)) -> ~ In X (tv (rename Y Y' t)).
Admitted.

Lemma ftv_lam_in_no_binder {B} Y X A t :
  In Y (ftv (@tmabs B X A t)) -> X <> Y.
Proof.
Admitted.

Lemma ftv_lam_no_binder {B} X A t :
  ~ In X (ftv (@tmabs B X A t)).
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

Lemma extend_ftv_keys_env_to_tv x sigma :
  In x (ftv_keys_env sigma) -> In x (tv_keys_env sigma).
Proof.
  intros.
  induction sigma.
  - inversion H.
  - destruct a as [a1 a2].
    unfold tv_keys_env.
    inversion H.
    + subst. apply in_eq.
    + apply in_cons.
      apply in_app_or in H0; destruct H0 as [H0 | H0].
      * apply extend_ftv_to_tv in H0.
        apply in_or_app. left. assumption.
      * apply in_or_app. right.
        apply IHsigma.
        assumption.
Qed.

Lemma extend_btv_to_tv x s :
  In x (btv s) -> In x (tv s).
Proof.
Admitted.

Lemma not_ftv_btv_then_not_tv x s :
  ~ In x (ftv s) -> ~ In x (btv s) -> ~ In x (tv s).
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
    unfold rename. simpl.
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
        assert (In X (tv t)).
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
  - unfold rename. simpl.
    unfold tv in HXtvt. fold tv in HXtvt.
    apply in_app_or in HXtvt.
    destruct HXtvt.
    + specialize (IHt1 H).
      unfold tv. fold tv.
      apply in_or_app. left. apply IHt1.
    + specialize (IHt2 H).
      unfold tv. fold tv.
      apply in_or_app. right. apply IHt2.
  - inversion HXtvt.
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
    unfold rename. simpl. rewrite <- String.eqb_neq in HXnotY.
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
    assert (Xftvt: In X (ftv t)).
    {
      unfold ftv in HXftvt. fold ftv in HXftvt.
      apply in_remove in HXftvt as [HXftvt0 HXftvt].
      assumption.
    }
    specialize (IHt Xftvt).
    destr_eqb_eq Y s.
    + rewrite ren_lam_vacuous. assumption.
    + rewrite ren_lam; auto.
      unfold ftv. fold ftv.
      apply Util.List.in_remove; auto.
  - unfold rename. simpl.
    unfold ftv in HXftvt. fold ftv in HXftvt.
    apply in_app_or in HXftvt.
    destruct HXftvt.
    + specialize (IHt1 H).
      apply in_or_app. left. apply IHt1.
    + specialize (IHt2 H).
      apply in_or_app. right. apply IHt2.
  - inversion HXftvt.
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
    unfold rename. simpl.
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
  - inversion HXftvt.
Qed.

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

Lemma btv_var_contradiction {x x'} :
  In x (btv (tmvar x')) -> False.
Admitted.

Lemma btv_lam {B X A t} :
  In X (btv (@tmabs B X A t)).
Proof.
  unfold btv.
  apply in_eq.
Qed.

Lemma not_btv_dc_lam {B X Y A t} :
  ~ In X (btv (@tmabs B Y A t)) -> ~ In X (btv t).
Admitted.

Lemma not_btv_dc_appl {B X t1 t2} :
  ~ In X (btv (@tmbin B t1 t2)) -> ~ In X (btv t1).
Admitted.

Lemma not_btv_dc_appr {B X t1 t2} :
  ~ In X (btv (@tmbin B t1 t2)) -> ~ In X (btv t2).
Admitted.

Lemma btv_c_lam {B X Y A t} :
  In X (btv t) -> In X (btv (@tmabs B Y A t)).
Admitted.

Lemma btv_c_appl {B X t1 t2} :
  In X (btv t1) -> In X (btv (@tmbin B t1 t2)).
Admitted.

Lemma btv_c_appr {B X t1 t2} :
  In X (btv t2) -> In X (btv (@tmbin B t1 t2)).
Admitted.

(* TV *)
Lemma not_tv_dc_lam {B X Y A t} :
  ~ In X (tv (@tmabs B Y A t)) -> ~ In X (tv t).
Admitted.

Lemma not_tv_dc_appl {B X t1 t2} :
  ~ In X (tv (@tmbin B t1 t2)) -> ~ In X (tv t1).
Admitted.

Lemma not_tv_dc_appr {B X t1 t2} :
  ~ In X (tv (@tmbin B t1 t2)) -> ~ In X (tv t2).
Admitted.

Lemma tv_c_lam {B X Y A t} :
  In X (tv t) -> In X (tv (@tmabs B Y A t)).
Admitted.

Lemma tv_c_appl {B X t1 t2} :
  In X (tv t1) -> In X (tv (@tmbin B t1 t2)).
Admitted.

Lemma tv_c_appr {B X t1 t2} :
  In X (tv t2) -> In X (tv (@tmbin B t1 t2)).
Admitted.

Lemma tv_dc_lam {B X Y A t} :
  In X (tv (@tmabs B Y A t)) -> In X (tv t).
Admitted.

(* FTV *)

Lemma ftv_c_appl {B X t1 t2} :
  In X (ftv t1) -> In X (ftv (@tmbin B t1 t2)).
Admitted.

Lemma ftv_c_appr {B X t1 t2} :
  In X (ftv t2) -> In X (ftv (@tmbin B t1 t2)).
Admitted.


Fixpoint btv_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => (btv t) ++ (btv_env sigma')
  end.

Lemma btv_env_helper (y : string) (t : term) sigma :
  In y (btv t) -> In t (map snd sigma) -> In y (btv_env sigma).
Proof.
Admitted.

Definition set_diff (l1 l2 : list string) : list string :=
  filter (fun x => negb (existsb (String.eqb x) l2)) l1.

Lemma btv_env_extends_to_tv_env x sigma :
  In x (btv_env sigma) -> In x (tv_keys_env sigma).
Admitted.

Lemma ftv_keys_env_extends_to_tv_env x sigma :
  In x (ftv_keys_env sigma) -> In x (tv_keys_env sigma).
Admitted.


Lemma ftv_keys_env__no_keys sigma x :
  ~ In x (ftv_keys_env sigma) -> ~ In x (map fst sigma).
Admitted.

Lemma ftv_keys_env__no_values sigma x :
  ~ In x (ftv_keys_env sigma) -> (forall val, In val (map snd sigma) -> ~ In x (ftv val)).
Admitted.

(* If x not a key or value, then not both*)
Lemma ftv_keys_env_helper sigma x :
  ~ In x (map fst sigma) -> (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) 
    -> ~ In x (ftv_keys_env sigma).
Admitted.

Lemma In_btv_env__exists sigma x :
  In x (btv_env sigma) -> exists t, In t (map snd sigma) /\ In x (btv t).
Proof.
  intros HIn.
  induction sigma.
  - inversion HIn.
  - destruct a as [a1 a2].
    simpl in HIn.
    apply in_app_or in HIn as [HIn | HIn].
    + exists a2. simpl. split. left. reflexivity. assumption. 
    + apply IHsigma in HIn as [t [HIn_t Hbtv_t]].
      exists t. split. simpl. right. auto. auto.
Qed.

Lemma btv_env_lookup__in σ x s t :
  lookup s σ = Some t -> In x (btv t) -> In x (btv_env σ).
Proof.
  intros Hl Hbtv.
  induction σ.
  - inversion Hl.
  - destruct a as [a1 a2].
    inversion Hl.
    destr_eqb_eq a1 s.
    + inversion H0; subst; clear H0.
      simpl in Hl.
      rewrite String.eqb_refl in Hl.
      simpl. apply in_app_iff. left. auto.
    + simpl in Hl.
      apply String.eqb_neq in H.
      rewrite H in Hl.
      simpl.
      apply in_app_iff.
      right.
      apply IHσ.
      auto.
Qed.


Lemma ftv_env_helper x σ s t :
  ~ In x (flat_map ftv (map snd σ)) -> lookup s σ = Some t -> ~ In x (ftv t).
Proof.
  intros HNin_σ Hl.
  induction σ.
  - inversion Hl.
  - destruct a as [a1 a2].
    simpl in HNin_σ.
    apply not_in_app in HNin_σ as [HNin_σ1 HNin_σ2].
    simpl in Hl.
    destr_eqb_eq a1 s.
    + inversion Hl; subst. auto.
    + apply IHσ; auto.
Qed.


Lemma btv_env_subset a sigma' sigma :
  incl sigma' sigma ->
  ~ In a (btv_env sigma) -> ~ In a (btv_env sigma').
Admitted.

