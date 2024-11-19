From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named STLC_named_typing ARS.
From PlutusCert Require Import alpha.


(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * type) -> list (string * type) -> Prop :=
  | calpha_nil : CAlpha [] [] []
  | calpha_cons sigma Gamma Gamma' x y K :
    CAlpha sigma Gamma Gamma' ->
    CAlpha ((x, y)::sigma) ((x, K)::Gamma) ((y, K)::Gamma').

(* Exercise and possibly useful *)
Lemma alpha_preserves_typing sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> Gamma |-* s : A -> Gamma' |-* t : A.
Proof.
  intros HAlpha Htype.
  generalize dependent A.
  generalize dependent Gamma.
  generalize dependent Gamma'.
  induction HAlpha.
  - intros Gamma' Gamma HCAlpha A HType.
    inversion HType.
    apply K_Var; subst...
    generalize dependent Gamma.
    generalize dependent Gamma'.
    induction a; subst...
    + intros.
      inversion HCAlpha; subst...
      assumption.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      inversion Hlookup.
      simpl.
      repeat rewrite Coq.Strings.String.eqb_refl.
      reflexivity.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      simpl.
      destruct (y =? w) eqn:yw.
      * apply String.eqb_eq in yw.
        contradiction.
      * specialize (IHa Gamma'0 Gamma0 H4).
        unfold lookup in Hlookup.
        destruct (x =? z) eqn:xz.
        -- apply String.eqb_eq in xz.
           contradiction.
        -- fold (lookup z Gamma0) in Hlookup.
          assert (Gamma0 |-* (tmvar z) : A).
          {
            (* Strengthening typing*)
            apply K_Var.
            assumption.
          }
           specialize (IHa H Hlookup).
           assumption.
  - intros Gamma' Gamma HCAlpha A0 HType.
    inversion HType.
    specialize (IHHAlpha ((y, A)::Gamma') ((x, A)::Gamma)
      (calpha_cons x y A HCAlpha) K2 H4).
    apply K_Lam.
    assumption.
  - intros Gamma' Gamma HCAlpha A HType. 
    inversion HType.
    specialize (IHHAlpha1 Gamma' Gamma HCAlpha (tp_arrow K1 A) H2).
    specialize (IHHAlpha2 Gamma' Gamma HCAlpha K1 H4).
    apply K_App with (K1 := K1); assumption.
Qed.


(* ********************
      Beta reduction
*)


(* TODO: Used to be Prop. Ask Jacco*)
Inductive step : term -> term -> Set :=
| step_beta (x : string) (A : type) (s t : term) :
    step (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step s1 s2 -> step (tmlam x A s1) (tmlam x A s2).

Lemma step_ebeta x A s t u : 
  u = ([x := t] s) -> step (tmapp (tmlam x A s) t) u.
Proof. move->. exact: step_beta. Qed.

Lemma de_morgan2 : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  intros P Q. split.
  - intros H. split.
    + intros HP. apply H. left. assumption.
    + intros HQ. apply H. right. assumption.
  - intros [H1 H2] [HP | HQ].
    + apply H1. assumption.
    + apply H2. assumption.
Qed.

Lemma ren_lam_vacuous x x' t s0 :
  rename x x' (tmlam x t s0) = tmlam x t s0.
Proof.
  unfold rename.
  simpl. rewrite String.eqb_refl. rewrite mren_id. reflexivity.
Qed.

Lemma ren_lam x x' t s s0 :
  x <> s -> rename x x' (tmlam s t s0) = tmlam s t (rename x x' s0).
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
Qed.

Lemma ren_two_vacuous {x Y' Y s }:
  x <> Y ->
  rename x Y' (rename x Y s) = rename x Y s.
Proof.

Admitted.

Lemma concat_not_eq_prefix (a b Y : string) :
  Y = String.append a b -> a <> "" -> Y <> b.
Proof.
  intros HY Ha.
  admit.
Admitted.

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

Lemma length_helper a b :
  (String.length (a ++ b)) = (String.length a + String.length b).
Proof.
Admitted.

Lemma length_concat_helper x xs :
  In x xs -> le (String.length x) (String.length (String.concat "" xs)).
Proof.
Admitted.

Lemma weaken_vacuous_alpha {X X' ren t t'} :
  Alpha ((X, X')::ren) t t' -> ~ In X (ftv t) -> ~ In X' (ftv t') -> Alpha ren t t'.
Proof.
  (* Proof will go something similar to alphaRenameStronger *)
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
      assert (In X (ftv (tmlam s t s0))).
      {
        unfold ftv. fold ftv.
        apply in_remove. split; auto.
      }
      contradiction.
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
Qed.


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
      apply in_remove; auto.
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

(*
What if we have (\x. y) (z). Then z in the ftv of the term, but after stepping it is not anymore.
So ftvs can be removed. But they can never be added.
*)
Lemma step_preserves_no_ftv s s' x :
  ~ In x (ftv s) -> step s s' -> ~ In x (ftv s').
Proof.
  intros Hnotins Hstep.
  induction Hstep.
  - unfold ftv.
  (*
    x notin ftv (tmapp (tmlam x0 A s) t).
    Suppose x <> x0.
    Then x notin ftv s.
    and x notin ftv t


    Suppose x = x0.
    then x notin ftv t.
    if x in ftv s, then it gets replaced by t, so x notin [x0 := t] s.
  *)
Admitted. 

(* One subsitution is related to the other through the alpha context*)
Inductive AlphaCtx : list (string * string) -> list (string * term) -> list (string * term) -> Prop :=
  | alpha_ctx_nil : AlphaCtx [] [] []
  | alpha_ctx_cons ren sigma sigma' x y t t' :
    AlphaVar ren x y ->
    Alpha ren t t' ->
    AlphaCtx ren ((x, t)::sigma) ((y, t')::sigma').

Lemma alpha_ctx_found ren sigma sigma' x x' t t' :
  AlphaCtx ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = Some t ->
  lookup x' sigma' = Some t' ->
  Alpha ren t t'.
Proof.
Admitted.

Lemma alpha_ctx_left_ex {ren sigma sigma' x x' t' }:
  AlphaCtx ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x' sigma' = Some t' ->
  { t & prod (lookup x sigma = Some t) (Alpha ren t t')}.
Proof.
Admitted.

Lemma alpha_ctx_right_ex {ren sigma sigma' x x' t }:
  AlphaCtx ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = Some t ->
  {t' & prod (lookup x' sigma' = Some t') (Alpha ren t t')}.
Proof.
Admitted.

Lemma alpha_ctx_ren_nil {sigma }:
  AlphaCtx [] sigma sigma.
Proof.
  induction sigma.
  - apply alpha_ctx_nil.
  - destruct a.
    apply alpha_ctx_cons.
    + apply alpha_var_refl.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.




Fixpoint ftv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (ftv t) ++ (ftv_keys_env sigma')
  end.


(* 
    Can there be a ftv in t that is equal to g2, then there is a problem?
    Suppose there is.
    Then this must be in the keys of sigma:
      - if it was not in the keys of sigma, it would still be in sigma [[t]]
      - so then it could not be equal to g2.
    .
    Since we also freshen over sigma, and thus over the keys of sigma,
    it can still not be equal to g2.
  *)
Lemma fresh2_subst_helper { Y sigma t } :
  ~ In Y (ftv (sigma [[t]])) -> ~ In Y (ftv_keys_env sigma) -> ~ In Y (ftv t).
Admitted.


  (*

  We know Alphactx ren sigma sigma'.
  g2 and g3 are both fresh over sigma and sigma', so no issue.

  But what if g2 and g3 not fresh over ren?

  well, let's look at a simpler case where sigma = [Z := t] and sigma' = [Z' := t']
  Suppose now g2 in ren. We have AlphaCtx ren sigma sigma'. Since g2 not in Z or t, we cannot have that there is a (g2, B) term with B in Z or t.
  Hence it is a vacuous one, and we can remove it.
  Do this for every g2 or g3 and we are left with a ren that does not contain any g2 or g3.
  Now we can add it and it does nott break shadowing :)
*)
Lemma alpha_ctx_ren_extend_fresh sigma sigma' x x' ren:
  ~ In x (tv_keys_env sigma) ->
  ~ In x' (tv_keys_env sigma') ->
  AlphaCtx ren sigma sigma' ->
  AlphaCtx ((x, x')::ren) sigma sigma'.
Admitted.

Lemma alpha_extend_fresh {x x' ren t t'}:
  ~ In x (ftv t) ->
  ~ In x' (ftv t') ->
  Alpha ren t t' ->
  Alpha ((x, x')::ren) t t'.
Proof.
Admitted.

(* TODO: SUPERSEDED BY alpha_ctx_ren_extend_fresh. The statements are almost identical (with respect to what we use them for) *)
(* TODO: t and t' are totall unrelevant here, how do I make them placeholders or something? *)
Lemma extend_alpha_ctx_fresh {x x' sigma sigma' sigma_ sigma_' ren t t'}:
  x = fresh2 (sigma_ ++ sigma) t ->
  x' = fresh2 (sigma_' ++ sigma') t' ->
  AlphaCtx ren sigma sigma' ->
  AlphaCtx ((x, x')::ren) sigma sigma'.
Admitted.

(* Most complex lemma up to now (12 nov) that is completely proved and general over arbitrary substitutions! *)
Lemma sub_vacuous' X t sigma sigma' s s' s'' ren ren1 ren2 :
  AlphaCtx ren sigma sigma' ->
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ~ In X (ftv s') -> Alpha ren (((X, t)::sigma) [[ s' ]]) (sigma' [[ s'' ]]).
Proof.
  intros HalphaSigma HalphaTrans Halphas1 Halphas2 Hnotins.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent s'.
  generalize dependent s''.
  induction s; intros s'' s' HxnotIns' ren2 Halphas2 ren1 Halphas1 ren HalphaSigma HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    simpl.
    subst.
    rewrite capms_equation_1.
    simpl.
    destr_eqb_eq X x.
    + apply not_in_cons in HxnotIns' as [xnotx].
      contradiction.
    + (* X <> x *)
      assert (AlphaVar ren x y0).
      {
        eapply alpha_var_trans; eauto.
      }
      destruct (lookup y0 sigma') eqn:y0sigma'.
      * destruct (lookup x sigma) eqn:xsigma.
        -- eapply alpha_ctx_found; eauto.
        -- exfalso.
           apply (alpha_ctx_left_ex HalphaSigma H0) in y0sigma'.
           destruct y0sigma' as [t' [y0sigma' Halpha] ].
           rewrite y0sigma' in xsigma.
           inversion xsigma.
    * destruct (lookup x sigma) eqn:xsigma.
      -- exfalso.
         apply (alpha_ctx_right_ex HalphaSigma H0) in xsigma as [t' [xsigma Halpha] ].
         rewrite xsigma in y0sigma'.
         inversion y0sigma'.
      -- apply alpha_var.
         assumption.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    subst.
    remember (fresh2 ((x, tmvar x) :: (X, t) ::sigma) s1) as s0'.
    remember (fresh2 ((y0, tmvar y0) :: sigma') s4) as s0''.
    apply alpha_lam.
    eapply IHs.
    + destr_eqb_eq X x.
      * remember (fresh2 ((x, tmvar x) :: (x, t) :: sigma) s1) as x'.
        apply ftv_not_in_after_rename.
        apply fresh2_over_key_sigma with (X := x) (s := t) in Heqx'.
        -- auto.
        -- apply in_cons. apply in_eq.
      * assert (~ In X (ftv s1)).
        {
          apply ftv_lam_negative in HxnotIns';
          auto.
        }
        apply ftv_not_in_rename.
        -- apply fresh2_over_key_sigma with (X := X) (s := t) in Heqs0'.
           ++ auto.
           ++ apply in_cons. apply in_eq.
        -- assumption.
    + eapply @alpha_trans with (ren := ((s, y0)::ren2)) (ren' := (y0, s0'')::(ctx_id_right ren2)).
      * apply alpha_trans_cons.
        apply id_right_trans.
      * exact H10.
      * change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
          apply alpha_extend_ids_right.    
          -- apply ctx_id_right_is_id.
          -- apply alphaRename. 
             apply fresh2_over_tv_term in Heqs0''.
             assumption.
    + eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
      * apply alpha_trans_cons.
        apply id_left_trans.
      * 
        change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
        apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- eapply alpha_sym.
          ++ apply alpha_sym_cons. apply alpha_sym_nil.
          ++ apply alphaRename.
             apply fresh2_over_tv_term in Heqs0'.
             assumption.
      * exact H2.
    + 
      eapply extend_alpha_ctx_fresh.
      * change ((x, tmvar x):: (X, t)::sigma) with (((x, tmvar x)::(X, t)::nil) ++ sigma) in Heqs0'.
        exact Heqs0'.
      * change ((y0, tmvar y0):: sigma') with (((y0, tmvar y0)::nil) ++ sigma') in Heqs0''.
        exact Heqs0''.
      * exact HalphaSigma.
    + apply alpha_trans_cons.
      exact HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    simpl.
    unfold ftv in HxnotIns'. fold ftv in HxnotIns'.
    apply not_in_app in HxnotIns' as [HxnotIns1 HxnotIns2].
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed.

(* Need alpha because the bigger vacuous substitution is used in fresh variable generation *)
Lemma sub_vacuous X t sigma s :
  ~ In X (ftv s) -> Alpha [] (((X, t)::sigma) [[ s ]]) (sigma [[ s ]]).
Proof.
  eapply sub_vacuous'; try apply alpha_refl; try constructor.
  - apply alpha_ctx_ren_nil.
Qed.

Lemma alpha_empty_sub s :
Alpha [] (nil [[s]]) s.
Proof.
  induction s.
  - rewrite capms_equation_1.
    simpl.
    apply alpha_var.
    apply alpha_var_refl.
  - rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(s, tmvar s)] s0) as s0'. 
    apply alpha_lam.
    (* Through transitivity and IH we would have to prove:
        [(s0' , s)] |- [] [[rename s s0' s0]] ~ [] [[s0]]
      *)
    (* PFFFF not easy to prove... Probably a corollary of ren_sub_compose_stronger_multiple
      But so trivial, I will believe it as fact! 
     *)
Admitted.

Lemma sub_vacuous_single X t s :
  ~ In X (ftv s) -> Alpha [] ([X := t] s) s.
Proof.
  intros Hxnotins.
  assert (Alpha nil (nil [[s]]) s).
  {
    apply alpha_empty_sub.
  }
  eapply alpha_trans.
  - apply alpha_trans_nil.
  - eapply sub_vacuous; auto.
  - assumption.
Qed.

Lemma sub_vacuous_single_stronger X t s s' ren :
  ~ In X (ftv s) -> Alpha ren s s' -> Alpha ren ([X := t] s) s'.
Proof.
Admitted.

(* Idk, but must be true. *)
Lemma tv_keys_env_helper y s sigma sigma_:
  y = fresh2 (sigma_ ++ sigma) s ->
  ~ In y (tv_keys_env sigma).
Proof.
Admitted.

Lemma cons_to_append {A } (x : A) sigma :
  (x :: sigma) = (x :: nil) ++ sigma.
Proof. reflexivity. Qed.

Lemma cons_chain_to_append {A } (x y : A) sigma :
(x :: y :: sigma) = (x :: y :: nil) ++ sigma .
Proof. reflexivity. Qed.

Hint Rewrite (@cons_to_append (string * term)) (@cons_chain_to_append (string * term)) : list_simpl.


(* Lemma tv_keys_env_helper_cons y s sigma  *)

Lemma subs_preserves_alpha'' sigma sigma' s : forall s' s'' ren1 ren2 ren,
  AlphaCtx ren sigma sigma' ->
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  Alpha ren (sigma [[s']]) (sigma' [[s'']]).
Proof.
  induction s; intros s'_ s''_ ren1_ ren2_ ren_ Hctx Htrans Halphas1 Halphas2.
  - admit.
  - 
Admitted.

Lemma subs_preserves_alpha' sigma sigma' s : forall s' s'' ren1 ren2 ren,
  AlphaCtx ren sigma sigma' ->
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  Alpha ren (sigma [[s']]) (sigma' [[s'']]).
Proof.
  induction s; 
  intros s'_ s''_ ren1_ ren2_ ren_ Hctx Htrans Ha_s1 Ha_s2;
  inversion Ha_s1 as [s' _1 _2 Hav_s1 |s' _1 _2 s0' _3 _4 Ha_s01 | sl' _1 sr' _2 _3 Ha_sl1 Ha_sr1 ]; subst;
  inversion Ha_s2 as [_1 s'' _2 Hav_s2 |_1 s'' _2 _3 s0'' _4 Ha_s02 | _1 sl'' _2 sr'' _3 Ha_sl2 Ha_sr2]; subst.
  - (* Case: tmvar *)
    rewrite capms_equation_1. 
    rewrite capms_equation_1.
  
    assert (Havs: AlphaVar ren_ s' s''). { eapply alpha_var_trans; eauto. }
      
    destruct (lookup s' sigma) eqn:xinsigma.
    + apply (alpha_ctx_right_ex Hctx Havs) in xinsigma as [t' [Hlookupy' Halphat ] ].
      now rewrite Hlookupy'.
    + destruct (lookup s'' sigma') eqn:y0insigma'.
      * apply (alpha_ctx_left_ex Hctx Havs) in y0insigma' as [t' [Hlookupx Halphat ] ].
        now rewrite Hlookupx in xinsigma.
      * now apply alpha_var.
  - (* Case: tmlam *)
    rewrite capms_equation_2; simpl.
    rewrite capms_equation_2; simpl.
    remember (fresh2 _ s0') as b'.
    remember (fresh2 _ s0'') as b''.
    apply alpha_lam.

    eapply IHs.
    + apply alpha_ctx_ren_extend_fresh; 
      auto;
      rewrite cons_to_append in Heqb';
      rewrite cons_to_append in Heqb'';
      eapply tv_keys_env_helper; eauto.
    + apply alpha_trans_cons; eauto.
    + eapply @alpha_trans with (ren := ((b', s')::nil) ++ (ctx_id_left ren1_)); eauto.
      * apply alpha_trans_cons.
        apply id_left_trans.
      * apply alpha_extend_ids_right.
        -- apply ctx_id_left_is_id.
        -- eapply alpha_sym.
           ++ apply alpha_sym_cons. apply alpha_sym_nil.
           ++ apply alphaRename.
              now apply fresh2_over_tv_term in Heqb'.
    + eapply @alpha_trans with (ren' := ((s'', b'')::nil) ++(ctx_id_right ren2_)); eauto.
      * apply alpha_trans_cons.
        apply id_right_trans.
      * apply alpha_extend_ids_right.
        -- apply ctx_id_right_is_id.
        -- apply alphaRename.
           now apply fresh2_over_tv_term in Heqb''.
           
  - (* Case: tmapp *)
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed.

Lemma subs_preserves_alpha sigma sigma' s s' ren :
  AlphaCtx ren sigma sigma' ->
  ren ⊢ s ~ s' ->
  Alpha ren (sigma [[s]]) (sigma' [[s']]).
Proof.
  intros.
  apply (@subs_preserves_alpha' sigma  sigma' s s s' (nil ++ ctx_id_left ren) ren ren); auto.
  - apply id_left_trans; auto.
  - apply alpha_extend_ids_right.
    + apply ctx_id_left_is_id.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.


Lemma ren_sub_compose_stronger_single : forall s s' s'' ren ren1 ren2 Z Z' t X X' Y,
  AlphaCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t ~ t ->
  AlphaVar ren X X'->
  AlphaVar ren Z Z' ->
  (* X string contained in Y: *)
  lt (String.length X) (String.length Y) ->
  Z <> Y /\ (~ In Y (tv s')) ->
  In X (ftv s') ->
  AlphaVar ren Y Y ->
  ren ⊢ [Z := t] (rename X Y s') ~ ((X', tmvar Y)::(Z', t)::nil) [[s'']].
Proof. 
  intros s s' s'' ren ren1 ren2 Z Z' t X X' Y Htrans HalphaS1 HalphaS2 Halphat HalphaX HalphaZ Hlength HZnotY  Hftv HalphaY.



  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.

  induction s; intros ren2 ren1 ren HalphaTrans Halphat HalphaVarX HalphaVarZ HalphaVarY s'' Halphas2 s' Halphas1 HYfresh Hftv.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    assert (AlphaVar ren x y0). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x X.
    + (* x = X, but alphaVar ren X y0, so alphaVar ren x y0. But AlphaVar ren X X', so y0 = X'*)
      unfold rename. unfold mren. simpl. rewrite String.eqb_refl.
      assert (Hy0X': y0 = X'). { eapply alphavar_unique; eauto. }
      rewrite capms_equation_1.
      simpl.
      destruct HYfresh as [HZnotY _].
      rewrite <- String.eqb_neq in HZnotY.
      rewrite HZnotY.
      rewrite capms_equation_1.
      simpl.
      rewrite Hy0X'.
      rewrite String.eqb_refl.
      apply alpha_var.
      assumption.

    + (* x <> X*)
      (* Contradiction: ftv (tmvar x) = x, and then X in x => X = x*)
      exfalso.
      unfold ftv in Hftv.
      apply in_inv in Hftv.
      destruct Hftv.
      * contradiction.
      * contradiction.
  - 
    inversion Halphas1.
   
    inversion Halphas2.
    subst.
    assert (HXnotx: X <> x).
    {
      intros HContra.
      rewrite HContra in Hftv.
      assert (~ In x (ftv (tmlam x t0 s1))) by apply ftv_lam_no_binder.
      contradiction.
    }

      rewrite ren_lam; [|assumption].
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 [(x, tmvar x); (Z, t)] (rename X Y s1)) as s0'.
      remember (fresh2 [(y0, tmvar y0);(X', tmvar Y); (Z', t)] s4) as s0''.
      apply alpha_lam.

      assert (In X (ftv s1)).
        {
          apply ftv_lam_helper in Hftv.
          assumption.
        }
      assert (In Y (tv (rename X Y s1))) by (now apply (ftv_tv_rename_helper) with (Y := Y) in H).

      assert (X <> s0').
      {
        clear IHs.
        intros HContra.

        assert (Hlengths0': gt (String.length s0') (String.length Y)).
        {
          unfold fresh2 in Heqs0'.
          assert (gt (String.length s0') (String.length (String.concat "" (tv (rename X Y s1))))).
          {
            admit. (* TODO: Changed fresh2 definition *)
            (* clear Heqs0''.
            rewrite Heqs0'.
            repeat rewrite length_helper.
            change (String.length "a") with 1.
            remember (String.length (String.concat "" (tv (rename X Y s1)))) as n.
            remember (String.length (x, tmvar x).1) as m1.
            remember (String.length (Z, t).1) as m2.
            remember (String.length "") as m3.
            remember (String.length (String.concat "" (flat_map (compose tv snd) [(x, tmvar x); (Z, t)]))) as m4.
            apply Nat.lt_le_trans with (m := 1 + n); auto.
            apply Nat.add_le_mono_l; auto.
            assert (le n (m4 + n)).
            {
              apply Nat.le_add_l.
            }
            assert (le (m4 + n) ((m3 + m2) + (m4 + n))).
            {
              apply Nat.le_add_l.
            }
            assert (le ((m3 + m2) + (m4 + n)) (m1 + ((m3 + m2) + (m4 + n)))).
            {
              apply Nat.le_add_l.
            }
            apply Nat.le_trans with (m := m4 + n); auto.
            apply Nat.le_trans with (m := (m3 + m2) + (m4 + n)); auto.
            rewrite <- Nat.add_assoc.
            rewrite <- Nat.add_assoc in H4.
            rewrite <- Nat.add_assoc.
            rewrite <- Nat.add_assoc.
            assumption. *)
          }
          unfold gt in H1.
          assert ( le (String.length Y)  (String.length (String.concat "" (tv (rename X Y s1))))). 
          { apply length_concat_helper. assumption. }
          unfold gt.
          apply Nat.le_lt_trans with (m := String.length (String.concat "" (tv (rename X Y s1)))); auto.
        }
        rewrite <- HContra in Hlengths0'.
        lia.
      }

      assert (s0' <> Y).
      {
        intros Hcontra.
        subst.
        symmetry in Hcontra.


        apply (fresh2_over_tv_term) in Hcontra.
        contradiction.
      }

      assert (Y <> x).
      {
        destruct HYfresh as [_ HYfresh].
        unfold tv in HYfresh.
        rewrite not_in_cons in HYfresh.
        destruct HYfresh as [HYfresh _].
        assumption.
      }

        rewrite ren_commute; try auto.
        eapply IHs.
        * apply alpha_trans_cons. exact HalphaTrans.
        * eapply (fresh2_over_tv_value_sigma) in Heqs0'; eapply (fresh2_over_tv_value_sigma) in Heqs0''.
          -- apply (alpha_not_in_tv_helper); eauto.
          -- apply in_cons. apply in_cons. apply in_eq.
          -- apply in_cons. apply in_eq.
          -- apply in_eq.
        * apply alpha_var_diff.
          -- auto.
          -- 
            eapply (fresh2_over_key_sigma Heqs0'').
            apply in_cons.
            apply in_eq.
          -- assumption.
        
        * apply alpha_var_diff.
          -- eapply (fresh2_over_key_sigma Heqs0').
             apply in_cons.
             apply in_eq.
          -- eapply (fresh2_over_key_sigma Heqs0'').
             apply in_cons.
             apply in_cons.
             apply in_eq.
          -- assumption.
        * apply alpha_var_diff.
           -- assumption.
           -- apply (fresh2_over_tv_value_sigma) with (X := X') (s := tmvar Y) in Heqs0''.
              ++ unfold tv in Heqs0''.
                 apply not_in_cons in Heqs0'' as [Hs0''NotY _].
                 assumption.
              ++ apply in_cons. apply in_eq.
           -- assumption.
      
        * eapply alpha_trans.
          -- apply alpha_trans_cons.
            apply id_right_trans.
          -- exact H10.
          -- change ((y0, s0''):: (ctx_id_right ren2)) with (((y0, s0'')::nil) ++ (ctx_id_right ren2)). 
            apply alpha_extend_ids_right.    
            ++ apply ctx_id_right_is_id.
            ++ apply alphaRename. 
              apply fresh2_over_tv_term in Heqs0''.
              assumption.
        * eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
          -- apply alpha_trans_cons.
            apply id_left_trans.
          --  
            change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
              apply alpha_extend_ids_right.
              ++ apply ctx_id_left_is_id.
              ++ eapply alpha_sym.
                ** apply alpha_sym_cons. apply alpha_sym_nil.
                ** apply alphaRename. 
                   (*
                    s0' <> tv (rename X Y s1). now, if we dont do the renaming, we can suddenly have only X extra in there. 
                    But also X <> s0'.
                   *)
                   assert (~ In s0' (tv (rename X Y s1))).
                   {
                    eapply fresh2_over_tv_term; eauto.
                   }

                   intros HContra.
                   clear IHs.
                   assert (s0' <> X).
                   {
                      auto.
                   }
                   apply (@tv_rename_vacuous_helper _ X Y _ (H6)) in HContra.
                   contradiction.
          -- assumption.

          
        * destruct HYfresh as [HZnotY HYfresh].

          split; [assumption|]. 
        
          admit. (* Y not in tv s1? Yes by Y notin tv (tmlam x t0 s1). Also Y <> x and Y <> s0'*)
        * assert (In X (ftv s1)).
        {
          apply ftv_lam_helper in Hftv.
          assumption.
         }
        
          apply (@ftv_rename_vacuous_helper _ x s0' _ HXnotx) in H5.

          assumption.
        
       - admit. 
  

Admitted.

Lemma in_cons_sum {A : Type} (x y : A) (l : list A) :
  In x (y :: l) -> sum (x = y) (In x l).
Proof.
Admitted. 

(* Analogous to in_app_or, but for set *)
Lemma in_app_sum {A : Type} (x : A) (l1 l2 : list A) :
  In x (l1 ++ l2) -> sum (In x l1) (In x l2).
Proof.
  intros Hin.
  induction l1 as [| a l1' IH].
  - (* Case: l1 is empty *)
    simpl in Hin.
    right; assumption.
  - (* Case: l1 is non-empty *)
    apply in_cons_sum in Hin.
    destruct Hin as [Hin | Hin].
    + left. subst. apply in_eq.
    + destruct (IH Hin) as [Hin_l1 | Hin_l2].
      * left; right; assumption.
      * right; assumption.
Qed.

Lemma alpha_rename_binder_stronger x y ren1 ren2 ren s s' s'' t t' :
  AlphaCtxTrans (ren1) ren2 (ren) ->
  Alpha ((x, y)::ren1) s' s ->
  Alpha ren2 s s'' ->
  Alpha ren t t' ->
  In x (ftv s') ->
  In y (ftv s) -> (* I think that follows from the alpha and In x (ftv s')*)
  In y (ftv s'') ->
  Alpha ren ([x := t] s') ([y := t'] s'').
Proof.
  intros HalphaTrans HalphaS1 HalphaS2 Halphat Hinxs' Hinys Hinys''.
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  induction s; intros ren2 ren1 ren HalphaTrans Halphat s'' HalphaS2 Hinys'' s' HalphaS1 Hinxs'.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    assert (Hyy1: y = y1).
    {
      unfold ftv in Hinys''.
      apply in_inv in Hinys''.
      destruct Hinys''.
      - symmetry. assumption.
      - contradiction.
    }
    assert (Hxx0: x = x0).
    {
      unfold ftv in Hinxs'.
      apply in_inv in Hinxs'.
      destruct Hinxs'.
      - symmetry. assumption.
      - contradiction.
    }
    subst.
    rewrite capms_equation_1.
    rewrite capms_equation_1.
    simpl.
    rewrite String.eqb_refl.
    rewrite String.eqb_refl.
    assumption.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(x0, tmvar x0); (x, t)] s1) as s0'.
    remember (fresh2 [(y1, tmvar y1); (y, t')] s4) as s0''.
    apply alpha_lam.
    assert (Hyins0: In y (ftv s0)).
    {
      apply ftv_lam_helper in Hinys.
      assumption.
    } 
    assert (Hyins'' : In y (ftv (rename y1 s0'' s4))).
    {
      remember Hinys'' as Hinys''copy. clear HeqHinys''copy.
      apply ftv_lam_helper in Hinys''. 
      apply ftv_rename_vacuous_helper.
      - intros Hcontra.
        subst.
        apply ftv_lam_no_binder in Hinys''copy.
        contradiction.
      - assumption.
    }
    assert (Hxins': In x (ftv (rename x0 s0' s1))).
    {
      remember Hinxs' as Hinxs'copy. clear HeqHinxs'copy.
      apply ftv_lam_helper in Hinxs'. 
      apply ftv_rename_vacuous_helper.
      - intros Hcontra.
        subst.
        apply ftv_lam_no_binder in Hinxs'copy.
        contradiction.
      - assumption.
    }

    specialize (IHs Hyins0 ((s, s0'')::ren2) ((s0', s)::ren1)).

    eapply IHs; clear IHs.
    + apply alpha_trans_cons.
      assumption.
    + apply alpha_extend_fresh.
      * eapply fresh2_over_tv_value_sigma in Heqs0'.
        -- eauto. 
          (* TODO: s0' notin tv t => s0' notin ftv t lemma*)
          admit. 
        -- apply in_cons. apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqs0''.
        -- eauto. admit.
        -- apply in_cons. apply in_eq.
      * assumption.
    + eapply @alpha_trans with (ren := ((s, y1)::ren2)) (ren' := ((y1, s0'')::(ctx_id_right ren2))).
      * apply alpha_trans_cons.
        -- apply id_right_trans.
      * exact H10.
      * change ((y1, s0''):: (ctx_id_right ren2)) with (((y1, s0'')::nil) ++ (ctx_id_right ren2)). 
        apply alpha_extend_ids_right.    
        -- apply ctx_id_right_is_id.
        -- apply alphaRename.
           apply fresh2_over_tv_term in Heqs0''.
           assumption.
    + assumption.
    + apply alpha_swap with (ren := (s0', s)::(x, y)::ren1).
      * apply lrs_start.
        -- eapply fresh2_over_key_sigma.
           ++ exact Heqs0'.
           ++ apply in_cons. apply in_eq.
        -- intros Hcontra.
           rewrite Hcontra in Hinys.
           apply ftv_lam_no_binder in Hinys.
           contradiction.
        -- apply legalRenSwap_id.
      * eapply @alpha_trans with (ren := (s0', x0)::(ctx_id_left ((x, y)::ren1))) (ren' := ((x0, s)::(x, y)::ren1)).
        -- apply alpha_trans_cons.
           apply id_left_trans.
        -- change ((s0', x0) :: (ctx_id_left ((x, y) :: ren1))) with (((s0', x0)::nil) ++ (ctx_id_left ((x, y) :: ren1))).
           apply alpha_extend_ids_right.
           ++ apply ctx_id_left_is_id.
           ++ eapply alpha_sym.
              ** apply alpha_sym_cons. apply alpha_sym_nil.
              ** apply alphaRename.
                 apply fresh2_over_tv_term in Heqs0'.
                assumption.
        -- assumption.
    + assumption.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    simpl.
    unfold ftv in Hinxs'.
    (* fold ftv in Hinxs'.
    apply in_app_or_set in Hinxs' as [Hinxs1 | Hinxs2].
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto. *)
Admitted.


(* If s in x gets renamed to y in s', 
    doing a substitution for x on s corresponds to a substitution for y on s'*)
Lemma alpha_rename_binder {y : string } {s : term} s' x t t' ren:
  Alpha ((x, y)::ren) s s' ->
  Alpha ren t t' ->
  Alpha ren ([x := t] s) ([y := t'] s').
Proof.
  intros Halphas Halphat.
  destruct (in_dec String.string_dec x (ftv s)).
  {
    assert (Hinys: In y (ftv s')). {
      apply alpha_in_ftv_helper2 in Halphas; auto.
    }

  eapply alpha_rename_binder_stronger; eauto.
  - apply id_right_trans.
  - change (ctx_id_right ren) with (nil ++ (ctx_id_right ren)). 
    apply alpha_extend_ids_right.
    + apply ctx_id_right_is_id.
    + apply alpha_refl.
      apply alpha_refl_nil.
  }
  {
    assert (Hnotinys: ~ In y (ftv s')). {
      apply alpha_not_in_ftv_helper2 in Halphas.
      - assumption.
      - assumption.
    }

    (* Three ingredients necessary for transitivity result *)
    assert (Alpha nil ([x := t] s) s).
    {
      apply sub_vacuous_single.
      assumption.
    }
    assert (Alpha ren s s').
    {
      apply @weaken_vacuous_alpha with (X' := y) (X := x); assumption.
    }
    assert (Alpha nil s' ([y := t'] s')).
    {
      eapply alpha_sym.
      - apply alpha_sym_nil.
      - apply sub_vacuous_single.
        assumption.
    }

    eapply alpha_trans.
    - apply id_left_trans.
    - apply alpha_extend_ids_right with (idCtx := ctx_id_left ren) in H.
      + exact H.
      + apply ctx_id_left_is_id.
    - eapply alpha_trans.
      + apply id_right_trans.
      + exact H0.
      + apply alpha_extend_ids_right with (idCtx := ctx_id_right ren) in H1.
        * exact H1.
        * apply ctx_id_right_is_id.
  }
Qed.

(* TODO: Probably need to prove this with strenghtened induction (non-empty context) for the lambda case *)
Lemma step_preserves_alpha {s} {s'} {t} ren :
  Alpha ren s t -> step s s' -> {t' & prod (step t t') (Alpha ren s' t')}.
Proof.
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H2. subst. 
    eexists.
    split.
    + apply step_beta.
    + now apply alpha_rename_binder.
  - 
    specialize (IHHstep ren s3 H2).
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    eexists (tmapp t' t2).
    split.
    + apply step_appL. assumption.
    + apply alpha_app; assumption.
  - specialize (IHHstep ren t4 H4).
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    eexists.
    split.
    + apply step_appR. exact IHHstep.
    + apply alpha_app; assumption.


  - specialize (IHHstep ((x, y)::ren) s3 H4).
  
  
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    exists (tmlam y A t').
    split.
    + apply step_abs.
      assumption.
    + apply alpha_lam.
      assumption.
Qed.


Lemma ren_sub_compose_instantiated X Y s sigma :
  Y = (fresh2 ((X, tmvar X)::sigma) s) ->
  nil ⊢ sigma [[rename X Y s]] ~ ((X, tmvar Y)::sigma) [[s]].
Proof.
  (* intros HYfresh.
  induction s.
  - admit.
  - rewrite ren_lam; auto.
  destruct (in_dec String.string_dec X (ftv s)).
  {
  (* 
    From HYfresh we can conclude: 
    When we have a term [Z := t] (tmlam x A s) we create a fresh var exactly equal to Y.
    and we know Y not in s, Y not in Z, Y not ini t
    
    ~ (In Y (tv ([Z := t] s))). ???
    and therefore 
  *)
  eapply ren_sub_compose_stronger_single; eauto; try constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - eapply length_helper; eauto.
  - admit.
  - admit.
  } *)
Admitted.     

Require Import Coq.Program.Equality.

Lemma merge_sub_stronger x2 y1 x4 y2 s1 s2 s3 s4 t sigma2 sigma4 ren ren12 ren24 ren23 ren34 :
  Alpha ren12 s1 (((x2, tmvar y2)::sigma2) [[s2]]) ->
  Alpha ren23 s2 s3 ->
  Alpha ren34 s3 s4 ->
  AlphaCtxTrans ren12 ren24 ren ->
  AlphaCtxTrans ren23 ren34 ren24 ->
  AlphaCtx ren24 sigma2 sigma4 ->
  AlphaVar ren24 x2 x4 ->
  Alpha ren t t ->
  AlphaVar ren12 y1 y2 ->
  In y1 (ftv s1) -> (* corollary of x2 in ftv (s2)*)
  In x4 (ftv s4) ->
  In x2 (ftv s2) ->
  Alpha ren ([y1 := t] s1) (((x4, t)::sigma4) [[s4]]).
Proof.
  intros.
  generalize dependent ren.
  generalize dependent ren12.
  generalize dependent ren24.
  generalize dependent ren23.
  generalize dependent ren34.
  generalize dependent s1.
  generalize dependent s2.
  generalize dependent s4.
  induction s3; intros s4 Hinx4 s2 Hinx2 s1 Hiny1 ren34 Halphas34 ren23 Halphas23 ren24 Htrans24 Hctx Halphax ren12 Halphas12 Halphay ren Htrans Halphat.
  - inversion Halphas34.
    inversion Halphas23.
    subst.
    rewrite capms_equation_1 in Halphas12.
    rewrite capms_equation_1.
    unfold ftv in Hinx4.
    apply in_inv in Hinx4.
    assert (y = x4).
    {
      apply in_inv in Hinx4.
      destruct Hinx4; try contradiction; auto.
    } 
    subst.
    assert (x2 = x0).
    {
      apply in_inv in Hinx2.
      destruct Hinx2; try contradiction; auto.
    } 
    subst.
    simpl.
    rewrite String.eqb_refl.
    simpl in Halphas12.
    rewrite String.eqb_refl in Halphas12.
    inversion Halphas12.
    subst.
    assert (y1 = x).
    {
      apply in_inv in Hiny1.
      destruct Hiny1; try contradiction; auto.
    } subst.
    rewrite capms_equation_1.
    simpl.
    rewrite String.eqb_refl.
    assumption.
  - inversion Halphas23.
    inversion Halphas34.
    subst.
    rewrite capms_equation_2 in Halphas12.
    simpl in Halphas12.
    inversion Halphas12.
    subst.
    remember (fresh2 ((x, tmvar x)::(x2, tmvar y2)::sigma2) s0) as b1.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(x0, tmvar x0); (y1, t)] s2) as b2.
    remember (fresh2 ((y0, tmvar y0)::(x4, t)::sigma4) s7) as b3.
    apply alpha_lam.
    eapply IHs3.
    + eapply ftv_lam_rename_helper; eauto.
    + eapply ftv_lam_rename_helper. eauto.
    + eapply ftv_lam_rename_helper; eauto.
    + eapply @alpha_trans with (ren' := (((y0, b3)::nil) ++ (ctx_id_right ren34))).
      * 
      apply alpha_trans_cons.
        eapply id_right_trans.
      * exact H10.
      * apply alpha_extend_ids_right.
        -- apply ctx_id_right_is_id.
        -- apply alphaRename.
           apply fresh2_over_tv_term in Heqb3.
           assumption.
    + 
    {
     eapply @alpha_trans with (ren := (((b1, x)::nil) ++ (ctx_id_left ren23))).
     - apply alpha_trans_cons.
       apply id_left_trans.
     - apply alpha_extend_ids_right.
        + apply ctx_id_left_is_id.
        + eapply alpha_sym; [repeat constructor |].
          apply alphaRename.
          apply fresh2_over_tv_term in Heqb1.
          exact Heqb1.
      - exact H2.
    }
    + apply alpha_trans_cons; eauto.
    + apply alpha_ctx_ren_extend_fresh.
      * eapply tv_keys_env_helper.
        (* now autorewrite with list_simpl in Heqb1.  *)
        exact Heqb1.
      * change ((y0, tmvar y0)::(x4, t)::sigma4) with (((y0, tmvar y0)::(x4, t)::nil) ++ sigma4) in Heqb3.
        eapply tv_keys_env_helper. exact Heqb3.
      * assumption.
    + apply alpha_var_diff.
      * apply fresh2_over_key_sigma with (X := x2) (s := tmvar y2) in Heqb1.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * apply fresh2_over_key_sigma with (X := x4) (s := t) in Heqb3.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * assumption.
    + 
    {
      eapply @alpha_trans with (ren := ((b2, x0)::nil) ++ (ctx_id_left ren12)).
      - apply alpha_trans_cons.
        apply id_left_trans.
      - apply alpha_extend_ids_right.
        + apply ctx_id_left_is_id.
        + eapply alpha_sym; repeat constructor.
          apply alphaRename.
          apply fresh2_over_tv_term in Heqb2.
          assumption.
      - exact H3.
    }
    + apply alpha_var_diff; auto.
      * apply fresh2_over_key_sigma with (X := y1) (s := t) in Heqb2.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * apply fresh2_over_tv_value_sigma with (X := x2) (s := tmvar y2) in Heqb1.
        -- intros Hcontra.
           subst.
           unfold tv in Heqb1.
           unfold not in Heqb1.
           assert (In y2 (y2::nil)).
            {
              apply in_eq.
            }
            apply Heqb1 in H.
            contradiction.
        -- apply in_cons. apply in_eq.
    + apply alpha_trans_cons.
      assumption.
    + apply alpha_extend_fresh; auto.
      * eapply fresh2_over_tv_value_sigma in Heqb2.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           generalize dependent Hcontra. 
           exact Heqb2.
        -- apply in_cons. apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqb3.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           generalize dependent Hcontra. 
           exact Heqb3.
        -- apply in_cons. apply in_eq.
  - inversion Halphas23.
    inversion Halphas34.
    subst.
    rewrite capms_equation_3 in Halphas12.
    simpl in Halphas12.
    inversion Halphas12.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    simpl.
    simpl in Hinx4.
    apply in_app_sum in Hinx4.
    destruct Hinx4. (* We need to differentiate between vacuous and non-vacuous substs unfortunately*)
    {
      admit.
    (* If y1 in ftv s2, then also x2 in ftv s0 and x4 in ftv s6 I think
      Then we can use the IH.
      
      If it is not, none of them are and we have vacuous substs.
      Suppose y1 in s2. Then by AlphaVar ren12 y1 y2, we have 
      y2 in ((x2, tmvar y2) :: sigma2) [[s0]].
      Hence x2 in s0.
      Since Alpha ren24 s0 s6, and Alphavar ren24 x2 x4, then x4 in s6.

      Other way around:
      If y1 not in s2, then y2 not in ((x2, tmvar y2) :: sigma2) [[s0]].
      Hence x2 not in s0.
      Since Alpha ren24 s0 s6 and AlphaVar ren24 x2 x4, also not x4 in s6.
      *)
    

    }
    {
      apply alpha_app.
      {
        (* IH1 *)
        destruct (in_dec String.string_dec x4 (ftv s6)) eqn:x4ins6.
        {
          assert (In x2 (ftv s0)) by admit.
          assert (In y1 (ftv s2)) by admit.
          eapply IHs3_1; clear IHs3_1; clear IHs3_2.
          - assumption.
          - exact ( H).
          - exact H0.
          - exact H8.
          - exact H3.
          - exact Htrans24.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
          - eauto.
        }
        {
          clear IHs3_1. clear IHs3_2.
          (* x4 notin ftv s6: all vacuous substs *)
          assert (~ In x2 (ftv s0)) by admit.
          assert (~ In y1 (ftv s2)) by admit.

          apply sub_vacuous_single_stronger; auto.
          eapply @alpha_trans with (ren := ren) (t := (sigma4 [[s6]])).
          - apply id_right_trans.
          - assert (Alpha ren12 s2 ((sigma2 [[s0]]))). { 
              assert (Alpha (nil ++ ctx_id_right ren12) (((x2, tmvar y2)::sigma2) [[s0]]) (sigma2 [[s0]])).
              {
                apply alpha_extend_ids_right.
                - apply ctx_id_right_is_id.
                - 
                eapply sub_vacuous; auto.
              }
              eapply alpha_trans; eauto. 
              + apply id_right_trans.
           }
            assert (Alpha ren24 s0 s6). { eapply alpha_trans; eauto. }
            eapply @alpha_trans with (ren := ren12) (ren' := ren24) (ren'' := ren) (s := s2) (t := sigma2 [[s0]]); eauto.
            eapply subs_preserves_alpha; auto.
          - change (ctx_id_right ren) with (nil ++ ctx_id_right ren).
            apply alpha_extend_ids_right.
            + apply ctx_id_right_is_id.
            + eapply alpha_sym; eauto.
              * apply alpha_sym_nil.
              * eapply sub_vacuous; auto.
        }
      }
      admit. (* Analogous *)
    }
    
Admitted.

Lemma in_tv_value_then_in_tv_keys_env y y1 t (sigma : list (string * term)) :
  In y (tv t) -> In (y1, t) sigma -> In y (tv_keys_env sigma).
Proof.
Admitted.

Lemma lookup_some_then_in y t (sigma : list (string * term)) :
  lookup y sigma = Some t -> In (y, t) sigma.
Admitted.

Lemma no_ftv_subs_helper' y s s' s'' sigma ren ren1 ren2 :
  AlphaCtxTrans ren1 ren2 ren ->
  ~ In y (tv s) ->
  ~ In y (tv_keys_env sigma) ->
  AlphaCtx ren sigma sigma ->
  AlphaVar ren y y ->
  Alpha ren1 s s' ->
  Alpha ren2 s' s'' ->
  ~ In y (ftv (sigma [[s'']])).
Proof.
  intros.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent s.
  generalize dependent s''.
  induction s'; intros s'' s_ Hynots ren2 Halphas2 ren1 Halphas1 ren Htrans Hctx Halphay.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    assert (Halphax0y1: AlphaVar ren x y1).
    {
      eapply alpha_var_trans; eauto.
    }
    assert (Hynotx0: y <> x).
    {
      intros Hcontra.
      subst.
      unfold tv in Hynots.
      contradiction Hynots.
      apply in_eq.
    }
    destruct (lookup y1 sigma) eqn:Hlookup.
    {
      assert (In (y1, t) sigma).
      {
        apply lookup_some_then_in in Hlookup.
        assumption.
      }
      intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      assert (In y (tv_keys_env sigma)).
      {
        
        eapply in_tv_value_then_in_tv_keys_env; eauto.
      }
      contradiction.
    }
    {
      simpl.

      destr_eqb_eq y1 y.
      - assert (Hx0y: y = x).
        {
          
          eapply alphavar_unique.
          - assert (Alpha ren (tmvar y) (tmvar y)).
            {
              apply alpha_var.
              assumption.
            }
            eapply alpha_sym in H.
            + inversion H.
              exact H5.
            + eapply sym_alpha_ctx_is_sym.
          - assert (Alpha ren (tmvar x) (tmvar y)).
          {
            apply alpha_var.
            assumption.
          }
          eapply alpha_sym in H.
          + inversion H.
            exact H5.
          + eapply sym_alpha_ctx_is_sym.
        }
        contradiction.
      - intros Hcontra.
        destruct Hcontra; contradiction.
    }
    
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    assert (Hnotys0: ~ In y (tv s1)).
    {
      simpl in Hynots.
      auto.
    } 
    rewrite capms_equation_2.
    simpl.
    subst.
    remember (fresh2 _ _) as b.

    (* If y = b, we are done by how remove works*)
    destr_eqb_eq y b.
    remember (fresh2 _ _) as b.
    {
      apply remove_In.
    }
    {
      (* y <> b*)
      rewrite <- in_remove.
      intros Hcontra'.
      
      (* We do an unnecessary allowed renaming here, since tv/ftv does not care about this*)
      remember (fresh2 ((y, tmvar y)::sigma) s1) as b'.
      assert (Hnotyreny1b's1: ~ In y (tv (rename x b' s1))).
      {
        apply tv_not_after_rename.
        - apply fresh2_over_key_sigma with (X := y) (s := tmvar y) in Heqb'.
          + auto.
          + apply in_eq.
        - assumption.
      }

      assert (~ In y (ftv (sigma [[rename y1 b s3]]))).
      {
        eapply IHs' with (s := rename x b' s1) (ren := ((b', b)::ren)).
        - assumption.
        - {
          eapply @alpha_trans with (ren' := ((y1, b)::nil) ++ (ctx_id_right ren2)).
          - apply alpha_trans_cons.
            apply id_right_trans.
          - exact H11.
          - apply alpha_extend_ids_right.
            + apply ctx_id_right_is_id.
            + apply alphaRename.
              apply fresh2_over_tv_term in Heqb.
              assumption.
        }
        - eapply @alpha_trans with (ren := ((b', x)::nil) ++ (ctx_id_left ren1)).
          + apply alpha_trans_cons.
            apply id_left_trans.
          + apply alpha_extend_ids_right.
            * apply ctx_id_left_is_id.
            * eapply alpha_sym; [repeat constructor |].
              apply alphaRename.
              apply fresh2_over_tv_term in Heqb'.
              assumption.
          + exact H3.
        - now apply alpha_trans_cons.
        - eapply alpha_ctx_ren_extend_fresh.
          + change ((y, tmvar y):: sigma) with (((y, tmvar y)::nil) ++ sigma) in Heqb'.
            now apply tv_keys_env_helper in Heqb'.
          + change ((y1, tmvar y1):: sigma) with (((y1, tmvar y1)::nil) ++ sigma) in Heqb.
            now apply tv_keys_env_helper in Heqb.
          + assumption.            
        - apply alpha_var_diff.
          + apply fresh2_over_key_sigma with (X := y) (s := tmvar y) in Heqb'.
            * assumption.
            * apply in_eq.
          + auto.
          + assumption.
      }

      destruct Hcontra' as [Hcontra' _].
      contradiction.
    }
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_3.
    simpl.
    intros Hcontra.
    apply in_app_sum in Hcontra.
    simpl in Hynots.
    apply not_in_app in Hynots.
    destruct Hynots as [Hynots1 Hynott1].
    destruct Hcontra.
    + eapply IHs'1 with (s := s1); eauto.
    + eapply IHs'2; eauto.
Qed.

Lemma no_ftv_subs_helper y s sigma :
  ~ In y (tv s) ->
  ~ In y (tv_keys_env sigma) -> (* should be tv*)
  ~ In y (ftv (sigma [[s]])).
Proof.
  intros.
  eapply (@no_ftv_subs_helper' y s s s sigma nil nil nil); eauto.
  - constructor.
  - apply alpha_ctx_ren_nil.
  - apply alpha_var_refl.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma ftv_sub_helper4 x x' y y' s s' s'' sigma sigma' ren1 ren2 ren :
  AlphaCtxTrans ren1 ren2 ren ->
  AlphaCtx ren sigma sigma' ->
  Alpha ren1 s s' ->
  Alpha ren2 s' s'' ->
  AlphaVar ren x x' ->
  AlphaVar ren y y' ->
  In x (ftv s) ->
  ~ In y (tv s) -> (* A free var can ber renamed to a name that is bound, then suddenly it is bound! Cannot happen because it is a capture-avoiding substitution, but adding this condition makes it possible to not need a stronger induciton hypothesis*)
  In y' (ftv (((x', tmvar y')::sigma') [[s'']])).
Proof.
  intros.
  generalize dependent s.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  induction s'; intros ren2 ren1 ren Htrans Hctx Halphax Halphay s'' Hs'' s0 Hs' Hxins Hynotins.
  - inversion Hs''.
    inversion Hs'.
    subst.
    rewrite capms_equation_1.
    simpl.
    assert (x = x1).
    {
      inversion Hxins; [auto | contradiction].
    }
    subst.
    (*
      AlphaVar ren x1 ~ x'. 
      but also
      AlphaVar ren x1 y0.
      Hence x' = y0.
    *)
    assert (x' = y0).
    {
      assert (AlphaVar ren x1 y0).
      {
        eapply alpha_var_trans; eauto.
      }
      apply (alphavar_unique Halphax) in H.
      assumption.
    }
    subst.
    rewrite String.eqb_refl.
    unfold ftv.
    apply in_eq.
  - inversion Hs'.
    inversion Hs''.
    subst. 
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 _ _) as b1.
    assert (x <> x0).
    {
      intros Hcontra.
      subst.
      apply ftv_lam_no_binder in Hxins.
      contradiction.
    }
    assert (y <> x0).
    {
      intros Hcontra.
      subst.
      unfold tv in Hynotins. fold tv in Hynotins.
      apply not_in_cons in Hynotins as [Hynotins _].
      contradiction.
    }
    assert (In y' (ftv (((x', tmvar y'):: sigma') [[rename y1 b1 s4]]))).
    {
      
      (* hmm again a rename...

      for s0 we can choose s1. We know x in ftv s1.
      Then we need ren1 |- s1 ~ s'.  => ren1 = (x0, s)::ren1

      So then y in ftv (((x, tmvar y) :: sigma ) [[s'']]).

      we need s' ~ s'' = rename y1 b1 s4.
      We know s' ~ s4 with [s, y1]::ren2.

      Then s' ~ rename y b1 s4 with [s, b1]::ren2.

      Then ren := (x0, b1)::ren

      So do we have AlphaVar (x0, b1)::ren x x'? => x <> x0. b1 <> x', so yes.
      Do we have AlphaVar (x0, b1)::ren y y'? => y' <> b1. But what if y = x0? Then y notin ftv (tmlam x0 t s1). 
      Fixed by new condition on y.

    AlphaCtx (x0, b1)::ren sigma sigma' ? We already have AlphaCtx ren sigma sigma'.
    We for sure do not have that, since x0 not fresh. So it could shadow something.
    But I think we can cheat it, by doing an unncessesary renaming of x0 to fresh2 ((x0, tmvar x0))::sigma) ?.
      
      *)
      remember (fresh2 ((x0, tmvar y)::sigma) s1) as b2.

      assert (In x (ftv s1)).
      {
        apply ftv_lam_helper in Hxins.
        assumption.
      }

      eapply IHs'.
      - apply alpha_trans_cons. exact Htrans.
      - eapply extend_alpha_ctx_fresh.
        + change ((x0, tmvar y) :: sigma) with (((x0, tmvar y)::nil) ++ sigma) in Heqb2.
          exact Heqb2.
        + change ((y1, tmvar y1)::(x', tmvar y') :: sigma') with (((y1, tmvar y1)::(x', tmvar y')::nil) ++ sigma') in Heqb1.
          exact Heqb1.
        + assumption.
      - apply alpha_var_diff.
        + apply fresh2_over_tv_term in Heqb2.
          
          apply extend_ftv_to_tv in H1.
          intros Hcontra.
          subst.
          contradiction.
        + eapply fresh2_over_key_sigma in Heqb1.
          * eauto.
          * apply in_cons. apply in_eq.
        + assumption.
      - (* 
          y not b2 by cheat b2!
          y' notin b1.
        *)
        apply alpha_var_diff; auto.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y) in Heqb2; eauto.
          * simpl in Heqb2.
            auto.
          * apply in_eq.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y') in Heqb1; eauto.
          * simpl in Heqb1.
            auto.
          * apply in_cons. apply in_eq.
      - eapply @alpha_trans with (ren' := (((y1, b1)::nil) ++ ctx_id_right ren2)).
        + apply alpha_trans_cons.
          apply id_right_trans.
        + exact H10.
        + apply alpha_extend_ids_right.
          * apply ctx_id_right_is_id.
          * apply alphaRename.
            apply fresh2_over_tv_term in Heqb1.
            assumption.
      - eapply @alpha_trans with (ren := (((b2, x0)::nil) ++ ctx_id_left ren1)).
        + apply alpha_trans_cons.
          apply id_left_trans.
        + apply alpha_extend_ids_right.
          * apply ctx_id_left_is_id.
          * eapply alpha_sym; [repeat constructor |].
            apply alphaRename.
            apply fresh2_over_tv_term in Heqb2.
            exact Heqb2.
        + exact H2.

      - apply ftv_rename_vacuous_helper; assumption.
      - apply tv_not_after_rename.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y) in Heqb2; auto.
          * simpl in Heqb2.
            auto.
          * apply in_eq.
        + simpl in Hynotins.
          auto.
    }
    (* y' <> b1 so we can remove the remove *)
    apply in_remove.
    split.
    + assumption.
    + eapply fresh2_over_tv_value_sigma with (s := tmvar y') in Heqb1; eauto.
      * simpl in Heqb1.
        auto.
      * apply in_cons. apply in_eq.
  - inversion Hs'.
    inversion Hs''.
    subst.
    rewrite capms_equation_3.
    simpl.
    simpl in Hynotins.
    apply not_in_app in Hynotins.
    destruct Hynotins as [Hynotins1 Hynotint1].

    apply in_app_iff.
    simpl in Hxins.
    apply in_app_sum in Hxins.
    destruct Hxins.
    + left.
      eapply IHs'1; eauto.
    + right.
      eapply IHs'2; eauto.
Qed.

(* We need condition X' not in sigma! 
   Also X' not in s *)
Lemma merge_sub : forall sigma sigma_ x y s t,
  y = fresh2 (sigma_ ++ sigma) s -> (* TODO: sigma_ is irrelevant, do I have to name it?*)
  nil ⊢ ([y := t] (((x, tmvar y)::sigma) [[s]])) ~ ((x, t)::sigma) [[s]].
Proof.
  intros.
  destruct (in_dec String.string_dec x (ftv s)).
  {
    assert (In y (ftv (((x, tmvar y)::sigma) [[s]]))).
    {
       eapply ftv_sub_helper4.
       - apply alpha_trans_nil.
       - apply alpha_ctx_ren_nil.
       - apply alpha_refl.
         apply alpha_refl_nil.
        - apply alpha_refl.
          apply alpha_refl_nil.
        - apply alpha_var_refl.
        - apply alpha_var_refl.
        - assumption.
        - apply fresh2_over_tv_term in H.
          assumption.
    }
    eapply merge_sub_stronger.
    - apply alpha_refl.
      apply alpha_refl_nil.
    - apply alpha_refl.
      apply alpha_refl_nil.
    - apply alpha_refl.
      apply alpha_refl_nil.
    - apply alpha_trans_nil.
    - apply alpha_trans_nil.
    - apply alpha_ctx_ren_nil.
    - apply alpha_var_refl.
    - apply alpha_refl.
      apply alpha_refl_nil.
    - apply alpha_var_refl.
    - assumption.
    - assumption.
    - assumption.
  }
  {
    assert (~ In y (ftv (sigma [[s]]))). {
      
      apply no_ftv_subs_helper; auto.
      - apply fresh2_over_tv_term in H.
        intros Hcontra.
        contradiction.
      - eapply tv_keys_env_helper. exact H.
    }
    eapply alpha_trans.
    - apply alpha_trans_nil.
    - apply subs_preserves_alpha.
      + apply alpha_ctx_ren_nil.
      + eapply sub_vacuous; eauto.
    - {
      eapply alpha_trans.
      - apply alpha_trans_nil.
      - apply sub_vacuous_single; auto.
      - eapply alpha_sym. apply alpha_sym_nil.
        eapply sub_vacuous; eauto.
    }
  }
Qed.

Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x sigma , IdSubst sigma -> IdSubst ((x, tmvar x)::sigma).

Lemma id_subst_preserves_alpha s sigma :
  IdSubst sigma -> nil ⊢ sigma [[s]] ~ s.
Proof.
  (* WE cannot use ren sub compose because no freshness *)
Admitted.

(* Since we have two substitutions on the righthand side, we have to pull a substitution into a lambda twice
  and get two renamings, hence we need another transitivity step around the substitution *)
Lemma commute_sub_stronger x s s' s'' ssub t sigma sigma' ren ren1 ren2 ren12 ren3 x' :
AlphaCtxTrans ren1 ren2 ren12 ->
AlphaCtxTrans ren12 ren3 ren ->
AlphaCtx ren sigma sigma' ->
Alpha ren1 s' s ->
Alpha ren2 s s'' ->
Alpha ren3 ([x' := t] s'') ssub ->
In x' (ftv s'') ->
In x (ftv s') ->
AlphaVar ren12 x x' ->
Alpha ren12 t t ->
Alpha ren (((x, sigma [[t]])::sigma) [[s']]) (sigma' [[ ssub ]]).
Proof. 
  intros Htrans12 Htrans Hctx Halphas' Halphas'' Halphassub Hftvs'' Hftvs' Halphax Halphat.
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ssub.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent ren.
  generalize dependent ren12.
  generalize dependent ren3.

  induction s; intros ren3 ren12 Halphax Halphat ren Htrans Hctx ren2 ren1 Htrans12 ssub s'' Halphas'' Halphassub Hftvs'' s' Halphas' Hftvs'.
  - inversion Halphas'.
    inversion Halphas''.
    subst.
    rewrite capms_equation_1.
    assert (x = x0).
    {
      unfold ftv in Hftvs'.
      inversion Hftvs'.
      - auto.
      - contradiction.
    }
    simpl.
    subst.
    rewrite String.eqb_refl.
    assert (x' = y0).
    {
      inversion Hftvs''.
      - auto.
      - contradiction.
    }
    rewrite capms_equation_1 in Halphassub.
    subst.
    simpl in Halphassub.
    rewrite String.eqb_refl in Halphassub.

    assert (Alpha ren t ssub). {
      eapply alpha_trans; eauto.
    }
    apply subs_preserves_alpha; auto.

  - inversion Halphas''; subst.
    inversion Halphas'; subst.
    rewrite capms_equation_2 in Halphassub.
    simpl in Halphassub.
    inversion Halphassub; subst.
    remember (fresh2 [(y, tmvar y); (x', t)] s2) as g1.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 ((x0, tmvar x0):: (x, sigma [[t]])::sigma) s1) as g2.
    remember (fresh2 ((y0, tmvar y0)::sigma') s4) as g3.
    apply alpha_lam.
    eapply IHs with (ren12 := ((g2, g1)::ren12)).
    + apply alpha_var_diff.
      * apply fresh2_over_key_sigma with (X := x) (s := sigma [[t]]) in Heqg2; auto.
        apply in_cons. apply in_eq.
      * apply fresh2_over_key_sigma with (X := x') (s := t) in Heqg1; auto.
        apply in_cons. apply in_eq.
      * assumption.
    + eapply alpha_extend_fresh.
      * assert (~ In g2 (ftv (sigma [[t]]))) by admit. (* fresh*)
        assert (~ In g2 (ftv_keys_env sigma)) by admit. (* fresh*)
        clear IHs.
        apply (fresh2_subst_helper H H0).
        
      * apply fresh2_over_tv_value_sigma with (X := x') (s := t) in Heqg1; auto.
        -- admit. (* g1 notin tv t, then also g1 notin ftv t*)
        -- apply in_cons. apply in_eq.
      * assumption.
    
      
    + apply alpha_trans_cons.
      eauto.
    + apply alpha_ctx_ren_extend_fresh. 
      * admit. (* fresh *)
      * admit. (* fresh *) 
      * assumption. 
    + apply alpha_trans_cons; eauto.
    + {
      eapply alpha_trans.
      - apply alpha_trans_cons.
        apply id_right_trans.
      - exact H4.
      - change ((y, g1):: (ctx_id_right ren2)) with (((y, g1)::nil) ++ (ctx_id_right ren2)). 
        apply alpha_extend_ids_right.    
        + apply ctx_id_right_is_id.
        + apply alphaRename. 
          apply fresh2_over_tv_term in Heqg1.
          assumption.
      }
    + {
      eapply @alpha_trans with (ren' := ((y0, g3)::nil) ++ (ctx_id_right ren3)).
      - apply alpha_trans_cons.
        apply id_right_trans.
      - exact H6.
      - apply alpha_extend_ids_right.
        + apply ctx_id_right_is_id.
        + apply alphaRename.
          apply fresh2_over_tv_term in Heqg3.
          assumption.
    }  
    + apply ftv_rename_vacuous_helper.
      * intros Hcontra.
        subst.
        assert (~ In y (ftv (tmlam y t0 s2))) by apply ftv_lam_no_binder.
        contradiction.
      * apply ftv_lam_helper in Hftvs''.
        assumption.
    + {
      eapply @alpha_trans with (ren := ((g2, x0)::nil) ++ (ctx_id_left ren1)).
      - apply alpha_trans_cons.
        apply id_left_trans.
      - apply alpha_extend_ids_right.
        + apply ctx_id_left_is_id.
        + eapply alpha_sym.
          * apply alpha_sym_cons. apply alpha_sym_nil.
          * apply alphaRename.
            apply fresh2_over_tv_term in Heqg2.
            assumption.
      - exact H2.
      }
    + apply ftv_rename_vacuous_helper.
      * intros Hcontra.
        subst.
        assert (~ In x0 (ftv (tmlam x0 t0 s1))) by apply ftv_lam_no_binder.
        contradiction.
      * apply ftv_lam_helper in Hftvs'.
        assumption.
  - (* Not supser straightforward. Have to case on vacuous substs*)
  
    admit.
Admitted.

(* Commute subst *)
(* [] ⊢ ((x, sigma [[t]]) :: sigma) [[s]] ~ sigma [[[x := t] s]] *)
Lemma commute_sub x s t sigma :
  Alpha nil (((x, sigma [[t]])::sigma) [[s]]) (sigma [[ [x := t] s]]).
Proof.
  destruct (in_dec String.string_dec x (ftv s)).
  - {
    eapply commute_sub_stronger;
      try solve [ constructor 
                | apply alpha_refl; constructor
                | auto ].
    apply alpha_ctx_ren_nil.
  }
  - {
    eapply alpha_trans.
    - apply alpha_trans_nil.
    - eapply sub_vacuous; eauto.
    - eapply subs_preserves_alpha.
      + apply alpha_ctx_ren_nil.
      + eapply alpha_sym; [ constructor | now eapply sub_vacuous_single ].
  }
Qed.

(* Why do we need this up to alpha equivalence?

  Because sub lemmas are up to alpha equivalence.
*)
Lemma step_subst {s t} : 
  step s t -> forall sigma : list (string * term), {alphaSigmaT : term & 
  prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))} .
Proof.
  intros Hstep. induction Hstep; intros sigma.
  - rewrite capms_equation_3.
    rewrite capms_equation_2. simpl.
    remember (fresh2 ((x, tmvar x)::sigma) s) as x'.
    eexists.
    split.
    + eapply step_beta.
    + 
    {
      eapply alpha_trans; eauto.
      - apply alpha_trans_nil.
      - eapply subs_preserves_alpha.
        + apply alpha_ctx_ren_nil.
        + eapply ren_sub_compose_instantiated; eauto.
      - eapply alpha_trans.
        + apply alpha_trans_nil.
        + eapply merge_sub.
          * change ((x, tmvar x)::sigma) with (((x, tmvar x)::nil) ++ sigma) in Heqx'.
            exact Heqx'.
        + eapply commute_sub.
    }
  - (* Left application *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    exists (tmapp (alphaSigmaS2) (sigma [[t]])).
    split.
    + rewrite capms_equation_3.
      apply step_appL.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * assumption.
      * apply alpha_refl.
        apply alpha_refl_nil.
  - (* Right applicaiton *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaT2  [Ht2Step Ht2Alpha] ].
    exists (tmapp (sigma [[s]]) alphaSigmaT2).
    split.
    + rewrite capms_equation_3.
      apply step_appR.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * apply alpha_refl.
        apply alpha_refl_nil.
      * assumption.
  - remember (fresh2 ((x, tmvar x)::sigma) s1) as x'.
    specialize (IHHstep ((x, tmvar x')::sigma)).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    assert (HalphaRenCompose: nil ⊢ (sigma [[rename x x' s1]]) ~ ((x, tmvar x')::sigma) [[s1]]).
    {
      eapply ren_sub_compose_instantiated; eauto.
    }
    assert( {alphaSigmaT : term & prod (step (sigma [[rename x x' s1]]) alphaSigmaT) (Alpha [] alphaSigmaS2 alphaSigmaT )}).
    {
      eapply step_preserves_alpha.
      - eapply alpha_sym.
        + apply alpha_sym_nil.
        + exact HalphaRenCompose.
      - exact Hs2Step.
    }
    destruct H as [alphaSigmaT [HalphaStep HalphaSigmaT] ].
    eexists.
    split. 
    + rewrite capms_equation_2. simpl.
      rewrite <- Heqx'.
      apply step_abs.
      exact HalphaStep.
    + rewrite capms_equation_2. simpl.

      remember (fresh2 ((x, tmvar x)::sigma) s2) as s0'.
      apply alpha_lam.
      assert (Alpha nil alphaSigmaT (((x, tmvar x')::sigma) [[s2]])).
      {
        eapply alpha_trans; eauto.
        - apply alpha_trans_nil.
        - eapply alpha_sym; eauto.
          + apply alpha_sym_nil.
      }
      eapply alpha_trans.
      * apply id_left_trans.
      * eapply alpha_ids.
        apply ctx_id_left_is_id.
      * eapply alpha_trans.
        -- apply id_left_trans.
        -- change (ctx_id_left [(x', s0')]) with (nil ++ (ctx_id_left [(x', s0')])).
           apply alpha_extend_ids_right.
           ++ apply ctx_id_left_is_id.
           ++ exact H.
        -- eapply alpha_trans.
           ++ apply id_right_trans.
           ++ eapply subs_preserves_alpha.
              ** apply alpha_ctx_cons.
                 apply alpha_var_diff.
                 --- (* by x' = fresh2 (x)*) admit.
                 --- admit. (* ?y = x also by fresh s0' <> x *) 
                 --- apply alpha_var_refl.
                 --- apply alpha_var.
                     apply alpha_var_cons.
                     +++ reflexivity.
                     +++ reflexivity.
              ** 
                  eapply alpha_extend_vacuous_single.
                  --- assert (~ In x' (ftv s1)) by admit. (* x' fresh over s1*)
                      apply (step_preserves_no_ftv H0) in Hstep.
                      assumption.
                  --- admit. (* fresh *)
            ++ change (ctx_id_right [(x', s0')]) with (nil ++ (ctx_id_right [(x', s0')])).
               apply alpha_extend_ids_right.
               ** apply ctx_id_right_is_id.
               ** eapply alpha_sym; eauto.
                  --- apply alpha_sym_nil.
                  --- eapply ren_sub_compose_instantiated; eauto.
Admitted.


Lemma step_subst_sigma sigma {s t} :
  step s t -> {alphaSigmaT : term & prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof.
  intros Hstep.
  apply step_subst.
  assumption.
Qed.

Inductive star {e : term -> term -> Set } (x : term) : term -> Set :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.


(** **** Many-Step Reduction *)
Definition red := @star step.



(* Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x). *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  (* move=> A B. apply: (star_trans (tmapp s2 t1)).
  - apply: (star_hom (tmapp^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR. *)
(* Qed. *)
Admitted.

Lemma red_abs x A s1 s2 : 
  red s1 s2 -> red (tmlam x A s1) (tmlam x A s2).
(* Proof. apply: star_hom => x' y'. exact: step_abs. Qed. *)
Proof. Admitted.



Lemma red_subst sigma {s} {t} : 
  red s t -> {alphaSigmaT : term & prod (red (sigma [[s]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof. 
  intros Hred.
  induction Hred. 
  - exists (sigma [[s]]). split.
    + apply starR.
    + apply alpha_refl. constructor.
  - 
    apply (step_subst_sigma sigma) in e.
    
    destruct IHHred as [alphaSigmaY [Hred' Halpha] ].
    destruct e as [alphaSigmaZ [Hstep HalphaZ] ].
    eexists.

    admit. (* Doable with some alpha arguments*)
Admitted.


(* Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed. *)

Global Hint Resolve red_app red_abs 
(* sred_hup  *)
: red_congr.

(* Lemma red_compat sigma tau s :
  sred sigma tau -> red ([x := sigma] s) ([x := tau] s).
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed. *)


(* NOTE: A little pen and paper study strongly suggests that this is still true for named. *)
(* NOTE: At first I would expect that it would step on the right hand side (instead of multistep=red)
    but it doesnt because of the following example:
    Let t1 = (\x.x)w and t2 = w (which steps by step_beta)
    Let s = \y. (\z. x) x
    Then [x := t1] s = \y. (\z. t1) t1 = \y. (\z. (\x.x) w) ((\x.x) w)
    And [x := t2] s = \y. (\z. t2) t2 = \y. (\z. w) w

    there is no single step from the first to the second, since we have to perform
    step_beta in two different places.
    *)

(* TODO: cant we make it a relation? mren rho1 (mren rho2 s) in Mren s*)
Lemma ren_comp rho1 rho2 s : exists rho', mren rho1 (mren rho2 s) = mren rho' s.
Proof.
  (* TODO: Figure out on pen and paper first.*)
Admitted.



Lemma rename_preserves_step x x' s t : 
step s t -> step (rename x x' s) (rename x x' t).
Proof.
  intros Hstep.
  induction Hstep.
  - destruct (x =? x0) eqn:xx0.
    + 
      assert (x = x0) by admit.
      subst.
      unfold rename.
      unfold mren. fold mren.
      assert (drop x0 [(x0, x')] = nil) by admit.
      rewrite H.
      rewrite mren_id.
      (* Since all x0 in s are replaced by t, we must turn the rhs into
        rename x0 x' [x0 := rename x0 x' t] s, exactly like lhs
      *)  
      assert (mren [(x0, x')] ([x0 := t] s) = [x0 := mren [(x0, x')] t] s) by admit.
      rewrite H0.
      apply step_beta.

    + 
    unfold rename.
    unfold mren. fold mren.
    assert (drop x0 [(x, x')] = ((x, x')::nil)) by admit.
    rewrite H.

    (* Bulk of the work: This is a special case of commute subst! *)
    assert (mren [(x, x')] ([x0 := t] s) = [x0 := mren [(x, x')] t] (mren [(x, x')] s)) by admit.
    rewrite H0.
    apply step_beta.
  - apply step_appL.
    assumption.
  - apply step_appR.
    assumption.
  - admit.
Admitted.

(* Strengthen IH for red_beta*)
Lemma red_beta_ren x s t1 t2 rho : step t1 t2 -> { someAlpha : term & prod (red ([x := t1] (mren rho s)) someAlpha)
            (Alpha [] someAlpha ([x := t2] (mren rho s))) }.
Proof.
  elim: s rho t1 t2 => [Y|Y K1 T_body IH|T1 IH1 T2 IH2] rho t1 t2 Hstep.
  - unfold mren.
    destruct (lookup Y rho) eqn: Hlookup.
    all: rewrite capms_equation_1.
    all: rewrite capms_equation_1.
    all: simpl.
    (* TODO: The two cases below are identical except for s vs Y*)
    + destruct (string_dec x s).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        (* apply star1. *)
        (* assumption. *)
        admit.
      * unfold lookup.
        destruct (x =? s);
        admit.
        (* -- apply star1.
           assumption.
        -- apply starR. *)
    + destruct (string_dec x Y).
      * rewrite e.
        unfold lookup.
        rewrite eqb_refl.
        admit.
        (* apply star1.
        assumption. *)
      * unfold lookup.
        destruct (x =? Y);
        admit.
        (* -- apply star1.
           assumption.
        -- apply starR. *)
  - (* lambda abstraction *)
    simpl.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(Y, tmvar Y);(x, t1)] (mren (drop Y rho) T_body)) as x'.
    remember (fresh2 [(Y, tmvar Y);(x, t2)] (mren (drop Y rho) T_body)) as x2. (* x' and x2 only equal if we dont look at bound vars*)
    remember (drop Y rho) as rho'.
    specialize (IH ((Y, x')::rho') t1 t2 Hstep).
    destruct IH as [someAlpha [HredAlpha Halpha] ].

    (* exists (tmlam x' K1 someAlpha). *)
    eexists.
    split.

    + apply red_abs.

      (* What if Y is in the RHS of rho' ?*)
      assert (HrenComp: rename Y x' (mren rho' T_body) = mren ((Y, x')::rho') T_body).
      {
        admit.
      }
      rewrite HrenComp.
      exact HredAlpha. 
    + apply alpha_lam.

      admit.
  - rewrite capms_equation_3.
    rewrite capms_equation_3.
    (* apply red_app.
    + apply IH1.
      assumption.
    + apply IH2.
      assumption.  *)
Admitted.

Lemma red_beta x s t1 t2 : step t1 t2 -> red ([x := t1] s) ([x := t2] s).
Proof. 
  intros Hstep.
  induction s.
  - admit.
  - rewrite capms_equation_2. simpl.
    rewrite capms_equation_2. simpl.
    remember (fresh2 [(x, t1)] s0) as s0'.
    remember (fresh2 [(x, t2)] s0) as s0''.
    (* apply red_abs. *)
    
  (* move=> h. 
  apply red_beta_ren with (rho := nil) (x := x) (s := s) in h.
  rewrite mren_id in h. *)
  (* assumption. *)
Admitted.

(* Strong Normalization *)

(* used to be prop *)
Inductive sn {e : term -> term -> Set } x : Set :=
| SNI : (forall y, e x y -> sn y) -> sn x.

(*
Intuition:
h x is strongly normalizing.
then every reduction sequence starting from (h x) is finite.
The first condition (e x y -> e (h x) (h y)) says that each step has a corresponding step under h.
So in extension, each reduction chain starting from x has a corresponding reduction chain starting from h x.

So, since h x is SN, every reduction chain starting from h x is finite.
Then, by the extension, every reduction chain starting from x is finite.
*)
Lemma sn_preimage {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> e (h x) (h y)) -> @sn e (h x) -> @sn e x.
Proof.

  move eqn:(h x) => v A B.
  generalize dependent h.
  generalize dependent x.
  elim: B => {} v _ ih x h eqn.
  intros A.
  apply: SNI => y /A.
  

  
  rewrite eqn => /ih. eauto.
  Qed.

Lemma sn_preimage_alpha {e : term -> term -> Set} (h : term -> term) x :
  (forall x y, e x y -> { a : term & prod(Alpha [] (h y) a) (e (h x) a) }) -> 
  @sn e (h x) -> { a2 : term & prod(Alpha [] x a2) (@sn e a2)}.
Proof.
  (* move eqn:(h x) => v A B. elim: B h x A eqn => {} v _ ih h x A eqn.
  eexists.
  split.
  - admit.
  - 
  apply: SNI => y /A. rewrite eqn => /ih. apply/ih; eauto. *)
Admitted.

Notation SN := (@sn step).

Lemma sn_closedL t s : SN (tmapp s t) -> SN s.
Proof. apply: (sn_preimage (h := tmapp^~t)) => x y. exact: step_appL. Qed.

Lemma sn_subst sigma s : SN (sigma [[s]]) -> SN s.
Proof.
Admitted.

(* Not sure yet how to use the step_subst lemma in this*)
Lemma sn_subst_alpha sigma s : SN (sigma [[s]]) -> {alphaS & prod (Alpha [] alphaS s) (SN alphaS)}.
Proof.
  (* intros H.
  apply sn_preimage_alpha in H. 
    - destruct H as [alphaS [Halpha Hsn] ].
    exists alphaS.
      split.
      + eapply alpha_sym.
        * constructor.
        * assumption.
      + assumption.
    - intros x y Hstep.
      apply (@step_subst_sigma x y sigma) in Hstep.
      destruct Hstep as [alphaSigmaT [Hred Halpha] ].
      exists alphaSigmaT.
      split.
      * eapply alpha_sym.
        -- constructor.
        -- assumption.
      * assumption. *)
Admitted.



(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Set.

Definition neutral (s : term) : bool :=
  match s with
    | tmlam _ _ _ => false
    | _ => true
  end.

Record reducible (P : cand) : Set := {
  p_sn : forall s, P s -> SN s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

(* **** The logical relation for proving Strong normalization, 
        strengthens the IH to say something about labmda bodies*)
Fixpoint L (T : type) : cand :=
  match T with
    | tp_base => SN 
    | tp_arrow A B => fun s => forall t, L A t -> L B (tmapp s t)
  end.

(* TODO: Compare with Inductive instantiation from normalisation in
  PLF: that has a cleaner definition, but restraints the order*)
Definition EL (Gamma : list (string * type)) 
          (sigma : list (string * term)) : Set :=
  forall x T, lookup x Gamma = Some T ->
    { t & prod (lookup x sigma = Some t) (L T t)}.

(* is true! *)
Lemma extend_EL (Gamma : list (string * type)) (sigma : list (string * term)) x T t :
  EL Gamma sigma -> L T t -> EL ((x, T) :: Gamma) ((x, t) :: sigma).
Proof.
Admitted.

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible SN.
Proof. 
  constructor; eauto using ARS.sn. by move=> s t [f] /f. 

  (*
  
  TODO INCOMPLETE
  
  *)
Admitted.
Global Hint Resolve reducible_sn : core.

Lemma reducible_var P x : reducible P -> P (tmvar x).
Proof. move/p_nc. apply=> // t st. inversion st. Qed.

Lemma L_reducible A :
  reducible (L A).
Proof with eauto using step.
  elim: A => /=[|A ih1 B ih2].
  - apply reducible_sn.
  - constructor.
    + move=> s h. apply: (@sn_closedL (tmvar "x")). apply: (p_sn (P := L B))...
      eapply h. eapply reducible_var; eauto.
    + move=> s t h st u la. apply: (p_cl _ (s := tmapp s u))...
    + move=> s ns h t la.
      have snt := p_sn ih1 la.
      elim: snt la => {} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      (* Note: Case L B ([x := t] s0. By using Autosubst's "inv" instead of normal inversion, this goal vanishes. Why? *) (* Todo: Think, this case doesn't happen in db variant*)
      * apply: ih3 => //. exact: (p_cl ih1) la _.
Qed.

Corollary L_sn A s : L A s -> SN s.
Proof. intros Las. assert (reducible (L A)) by apply (L_reducible A).
   apply (p_sn H). assumption.
Qed.

Corollary L_cl T s t : L T s -> step s t -> L T t.
Proof.
  intros Hstep Hst.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_cl H Hstep); assumption.
Qed.

Corollary L_nc T s :
  neutral s -> (forall t, step s t -> L T t) -> L T s.
Proof. 
  intros Hneut Hstep.
  assert (H: reducible (L T)) by apply L_reducible.
  apply (p_nc H); assumption.
Qed.

Corollary L_var T x : L T (tmvar x).
Proof.
  apply L_nc; first by []. intros t st. inversion st.
Qed. 

Corollary L_cl_star T s t :
  L T s -> red s t -> L T t.
Proof.
  intros Ls red_st. induction red_st.
  - assumption.
  - apply L_cl with y; assumption.
Qed.

(* Closure under beta expansion. *)
Lemma beta_expansion A B x s t :
  SN t -> L A ([x := t] s) ->
  L A (tmapp (tmlam x B s) t).
Proof with eauto.
  move=> snt h. have sns := sn_subst (L_sn h).
  elim: sns t snt h => {} s sns ih1 t. elim=> {} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl h _. admit. (* exact: step_subst. *) (* need to alphafy this lemma *)
  - apply: ih2 => //. apply: L_cl_star h _. exact: red_beta.
Admitted.

Lemma beta_expansion_subst X t sigma s A B :
  SN t -> L A (((X, t)::sigma) [[s]]) -> L A (tmapp (sigma [[tmlam X B s]]) t).
Proof.
  intros snt H.
  remember (fresh2 ((X, tmvar X)::sigma) s) as X'.
  assert (L A ([X' := t] (sigma [[(rename X X' s)]])) -> L A (tmapp (tmlam X' B (sigma [[rename X X' s]])) t)).
  {
    apply beta_expansion; assumption.
  }

  (* Now we use H to show the assumption of H0 holds. Then we rewrite the conclusion into the goal*)
  assert (HsigIntoLam: tmapp (tmlam X' B (sigma [[rename X X' s]])) t = tmapp (sigma [[tmlam X B s]]) t).
  {
    rewrite capms_lam.
    rewrite HeqX'.
    reflexivity.
  }
  rewrite <- HsigIntoLam.
  apply H0.
  admit.
  (* rewrite composeCapms.
  - rewrite capmsRename.
    assumption.
  - rewrite -> HeqX'.
    (* apply freshLemma. easy by freshness*)
    admit. *)
Admitted.

(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_type : list (string * type) -> term -> type -> Set :=
  | K_Var : forall Δ X K,
      List.lookup X Δ = Some K ->
      Δ |-* (tmvar X) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (tmlam X K1 T) : (tp_arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (tp_arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (tmapp T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_type Δ T K).

(* The fundamental theorem. *)
Theorem soundness Gamma s A :
  has_type Gamma s A -> forall sigma,
    EL Gamma sigma -> L A (sigma [[s]]).
Proof with eauto using L_sn. 
  elim=> {Gamma s A} [Gamma X A |Gamma X A s B _ ih sigma EL|Gamma s t A B _ ih1 _ ih2 sigma HEL].
  - intros HlookupGamma sigma HEL.
    unfold EL in HEL.
    specialize (HEL X A HlookupGamma).
    destruct HEL as [t [HlookupSigma LAt] ].
    apply capms_var in HlookupSigma.
    rewrite HlookupSigma.
    assumption.
  - move=> t h.
    specialize (ih ((X, t)::sigma) (extend_EL EL h)).
    apply: beta_expansion_subst...
  - specialize (ih1 _ HEL). specialize (ih2 _ HEL).
    unfold L in ih1. fold L in ih1. specialize (ih1 (sigma [[t]]) ih2).
    rewrite capms_equation_3.
    assumption.
Admitted.

(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * type)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.



(* The identity substitution is in the EL relation *)

Lemma id_subst_EL :
  forall (E : list (string * type)),  EL E (id_subst E).
Proof.
Admitted.

(* TODO id_ren E could just be []? *)
Lemma id_subst_alpha_type E s T :
  has_type E s T -> Alpha [] s ((id_subst E) [[s]]).
Proof.
Admitted.

(* The fundamental theorem for named variables. *)
Corollary type_L (E : list (string * type)) s T : has_type E s T -> L T (id_subst E [[s]]).
Proof.
  intros Htype.
  assert (HEL: EL E (id_subst E)) by apply id_subst_EL.
  assert (Hsound: L T ((id_subst E) [[s]])) by apply (soundness Htype HEL).
  assumption.
Qed.

Corollary strong_normalization_alpha E s T : has_type E s T -> SN (id_subst E [[s]]).
Proof.
  intros Hty.
  apply type_L in Hty.
  apply L_sn in Hty.
  assumption.
Qed.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

Fixpoint is_normal (t : term) : bool :=
  match t with
  | tmlam X K T => is_normal T
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  end

with is_neutral (t : term) : bool :=
  match t with
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  | _ => false
  end.

  (** Normal types *)
Inductive normal_Ty : term -> Prop :=
  | NO_TyLam : forall x K T,
      normal_Ty T ->
      normal_Ty (tmlam x K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T

with neutral_Ty : term -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (tmvar X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (tmapp T1 T2).

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).

(* Deterministic step *)
Fixpoint step_d_f (t : term) : option term :=
    match t with
    | tmvar i => None
    | tmapp s t => 
        if is_normal s then
            if is_normal t then
                match s with
                | tmlam x A s' => Some ([x := t] s')
                | _ => None
                end
            else step_d_f t >>= fun t' => Some (tmapp s t')
        else step_d_f s >>= fun s' => Some (tmapp s' t)
    | tmlam x A s => (* step' s >>= _ does the normality check for us implicitly*)
        step_d_f s >>= fun s' => Some (tmlam x A s')
    end.

Inductive step_d : term -> term -> Set :=
| step_beta_d (x : string) (A : type) (s t : term) :
    normal_Ty s ->
    normal_Ty t ->
    step_d (tmapp (tmlam x A s) t) ([x := t] s)
| step_appL_d s1 s2 t :
    step_d s1 s2 -> step_d (tmapp s1 t) (tmapp s2 t)
| step_appR_d s t1 t2 :
    normal_Ty s ->
    step_d t1 t2 -> step_d (tmapp s t1) (tmapp s t2)
| step_abs_d x A s1 s2 :
    step_d s1 s2 -> step_d (tmlam x A s1) (tmlam x A s2).


(* step_nd is a subset of step
This is not true since step_d should use a different kind of substitution (only freshening when necessary)
*)
Lemma step_d_implies_step t t' : step_d t t' -> step t t'.
Proof.
  (* elim=> H; constructor; try assumption. *)
Abort.

Lemma step_d_implies_step_alpha t t' : step_d t t' -> { t'_alpha : term & prod(Alpha [] t' t'_alpha) (step t t'_alpha)}.
Proof.
  intros Hstep.
  induction Hstep.
  - (* this is proving that if substituteTCA x t s is alpha to [x := t] s (capmsfr)*) admit.
  - admit.
  - admit.
  - destruct IHHstep as [IHHt' [IHHalpha IHHstep'] ].
    exists (tmlam x A IHHt').
    split.
    + apply alpha_lam.
      apply alpha_extend_id'.
      * assumption.
      * apply not_break_shadow_nil.
    + apply step_abs.
      assumption.
Admitted.

(* Does this still work now we no longer have step_d_implies_step?
  Maybe if we make it up to alhpa
 *)
Lemma SN_d : forall t, (@sn step) t -> {t_alpha : term & prod (Alpha [] t t_alpha) ((@sn step_d) t_alpha)}.
Proof.
  intros t HSN.
  induction HSN.
  eexists.
  split.
  - admit.
  - (* oof. I dont know how to prove this. Maybe we need a weaker SN notion or something:
    @sn step_d x -> exists z, Alpha [] x z AND forall y, step z y -> SN y
   *)
Admitted.

(* Main lemma for going from using t alpha t' in SN t' to SN t*)
Lemma step_preserves_alpha_d sigma s t s' t' :
  Alpha sigma s t -> step_d s s' -> step_d t t' -> Alpha sigma s' t'.
Proof.
Admitted.

Require Import Coq.Program.Equality.

(*I do not like these lemmas. Maybe we can change the definition of normality to equal not being able to step? *)
Lemma is_normal_no_step_d t :
  is_normal t = true -> step_d_f t = None.
Proof.
Admitted.

Lemma is_normal_then_step_d t :
  is_normal t = false -> ~ step_d_f t = None.
Proof.
Admitted.

(* We also need this for sound/completeness, so we can assume it is true/a good approach*)
Lemma is_normal_then_normal_Ty t : 
  is_normal t = true -> normal_Ty t.
Proof.
Admitted.


Lemma step_d_f_to_step_d : forall t t', step_d_f t = Some t' -> step_d t t'.
Proof.
  intros t t' Hstep_d_f.
  dependent induction t. (* we needed IH over t' *)
  - discriminate.
  - destruct (is_normal t0) eqn: Hnormal_s.
    + apply is_normal_no_step_d in Hnormal_s.
      inversion Hstep_d_f.
      rewrite Hnormal_s in H0.
      inversion H0.
      (* If t0 is normal, then also tmlam s t t0*)
    + destruct (step_d_f t0) eqn: Hstep_t.
      * inversion Hstep_d_f.
        rewrite Hstep_t in H0.
        inversion H0.
        apply step_abs_d.
        specialize (IHt t1).
        apply IHt.
        reflexivity.
      * apply is_normal_then_step_d in Hnormal_s.
        contradiction.
  - inversion Hstep_d_f.
    destruct (is_normal t1) eqn: Hnormal_s.
    + destruct (is_normal t2) eqn: Hnormal_t.
      * destruct t1. (* case step_beta *)
        -- discriminate.
        -- inversion Hnormal_s.
           inversion Hnormal_t.
           inversion H0.
           apply step_beta_d.
           ++ apply is_normal_then_normal_Ty.
              assumption. (* is_normal -> normal_ty, we need that anyway for sound/completeness*)
           ++ apply is_normal_then_normal_Ty.
              assumption.
        -- discriminate.
      * destruct (step_d_f t2) eqn: Hstep_t. (* IH was not strong enough, so dependent induction *)
        -- inversion H0.
           apply step_appR_d.
           ++ apply is_normal_then_normal_Ty.
              assumption.
           ++ apply IHt2. 
              reflexivity.
        -- discriminate.
    + destruct (step_d_f t1) eqn: Hstep_s.
      * inversion H0.
        apply step_appL_d.
        apply IHt1.
        reflexivity.
      * discriminate.
Qed.

(* eq_refl didnt work, this does, thank Copilot, but I dont understand *)
Lemma eq_proof {A : Type} (x : A) : x = x.
Proof. reflexivity. Qed.

(* Terminating normalization procedure helper.
  We can normalize a term given that we know that an 
  alpha equivalent term is strongly normalizing
*)
Fixpoint normalizer' {sigma : list (string * string)} (t t' : term) (HAlpha : Alpha sigma t t') (HSN : (@sn step_d) t') : term :=
  match step_d_f t as res return (step_d_f t = res -> term) with
  | None => fun _ => t
  | Some t1 => fun Hstep =>
      match step_d_f t' as res' return (step_d_f t' = res' -> term) with
      | None => fun _ => t1 (* Uhm. Cannot happen. How to show this to coq? *)
      | Some t'1 => fun Hstep' =>
          let HStep_d := step_d_f_to_step_d Hstep in
          let HStep_d' := step_d_f_to_step_d Hstep' in
          let HAlpha' := step_preserves_alpha_d HAlpha HStep_d HStep_d' in
          let HSN' := match HSN with
                      | SNI f => f t'1 HStep_d'
                      end in
          @normalizer' sigma t1 t'1 HAlpha' HSN'
      end (eq_proof (step_d_f t'))
  end (eq_proof (step_d_f t)).

(* Normalization procedure for well typed terms *)
Definition normalizer E T (t : term) (Htype : has_type E t T) : term :=
  let t' := id_subst E [[t]] in
  let HAlpha := @id_subst_alpha_type E t T Htype in
  let HSN := strong_normalization_alpha Htype in
  let (t'', p ) := SN_d HSN in
  let (HAlpha', SNstep_d_t'') := p in

    (* HAlpha says Alpha [] t t'
       HAlpha' says Alpha [] t' t''
       
    Hence by transitivity: Alpha [] t t''
    *)
  let HAlphaTrans := alpha_trans alpha_trans_nil HAlpha HAlpha' in
      @normalizer' [] t t'' HAlphaTrans SNstep_d_t''.


(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)


*)