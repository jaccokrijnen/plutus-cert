
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List Util.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

From PlutusCert Require Import 
  construct_GU 
  step_naive 
  psubs 
  util 
  STLC GU_NC 
  Alpha.alpha 
  variables 
  alpha_subs 
  alpha_freshness.

Lemma not_ftv_to_not_tv {x s}:
  ~ (In x (ftv s)) -> prod (~ (In x (tv (to_GU'' x s)))) (Alpha [] s (to_GU'' x s)).
Proof.
  intros.
  split.
  - apply not_ftv_btv_then_not_tv.
    + eapply @alpha_preserves_no_ftv with (x := x) (s := s); auto.
      apply to_GU''__alpha. constructor.
    + apply to_GU''__btv.
  - apply to_GU''__alpha.
Qed.


Lemma alpha_extend_vacuous_ftv {x x' s s' R}:
  ~ (In x (ftv s)) -> ~ (In x' (ftv s')) -> Alpha R s s' -> Alpha ((x, x')::R) s s'.
Proof.
  intros.
  apply not_ftv_to_not_tv in H as [Htv_s Ha_s].
  apply not_ftv_to_not_tv in H0 as [Htv_s' Ha_s'].
  assert (Alpha R (to_GU'' x s) (to_GU'' x' s')). {
    apply @alpha_trans3 with (s' := s) (s'' := s'); auto.
    eapply @alpha_sym. constructor. auto.
  }
  apply @alpha_trans3 with (s' := to_GU'' x s) (s'' := to_GU'' x' s') (s''' := s'); auto.
  - apply alpha_extend_vacuous; auto.
  - eapply @alpha_sym. constructor. auto.
Qed.

Lemma alpha_vacuous_R {s s' R1 R2}:
  (forall x, In x (map fst R1) -> (~ In x (ftv s))) -> (forall x', In x' (map snd R1) -> ~ In x' (ftv s')) -> Alpha R2 s s' -> Alpha (R1 ++ R2) s s'.
Proof.
  intros.
  induction R1.
  - rewrite app_nil_l. auto.
  - destruct a as [a1 a2].
    apply alpha_extend_vacuous_ftv.
    + apply H. apply in_eq.
    + apply H0. apply in_eq.
    + apply IHR1.
      * intros. eapply H. apply in_cons. auto.
      * intros. eapply H0. apply in_cons. auto.
Qed.

Require Import Coq.Program.Equality.

Lemma αctx_vacuous_R R σ σ' :
  (forall x, In x (map fst R) -> (~ In x (ftv_keys_env σ))) -> (forall x', In x' (map snd R) -> ~ In x' (ftv_keys_env σ')) -> alphaSubs [] σ σ' -> alphaSubs R σ σ'.
Proof.
  intros Hvac1 Hvac2 Ha.
  dependent induction σ.
  - inversion Ha; subst. constructor.
  - inversion Ha; subst.
    constructor.
    + eapply IHσ; eauto; intros.
      * 
        specialize (Hvac1 x0 H).
        simpl in Hvac1. apply de_morgan2 in Hvac1 as [_ Hvac1].
        apply not_in_app in Hvac1 as [_ Hvac1]. auto.
      * specialize (Hvac2 x' H).
        simpl in Hvac2. apply de_morgan2 in Hvac2 as [_ Hvac2].
          apply not_in_app in Hvac2 as [_ Hvac2]. auto.
    + inversion H3; subst.
      apply alphavar_refl_weaken_vacuouss. 
      * intros Hcontra.
        apply Hvac1 in Hcontra. simpl in Hcontra. 
        apply de_morgan2 in Hcontra as [Hcontra _].
        contradiction.
      * intros Hcontra.
        apply Hvac2 in Hcontra. simpl in Hcontra. 
        apply de_morgan2 in Hcontra as [Hcontra _].
        contradiction.
    + assert (Alpha (R ++ nil) t t').
      { apply alpha_vacuous_R.
        - intros.
        apply Hvac1 in H. simpl in H. apply de_morgan2 in H as [_ H].
        apply not_in_app in H as [H _]. auto.
        - intros.
        apply Hvac2 in H. simpl in H. apply de_morgan2 in H as [_ H].
        apply not_in_app in H as [H _]. auto.
        - auto.
      }
      rewrite app_nil_r in H.
      auto.
Qed.
(* END OF THAT*)


Lemma alpha_extend_fresh_tv {x x' ren t t'}:
  ~ In x (tv t) ->
  ~ In x' (tv t') ->
  Alpha ren t t' ->  

  Alpha ((x, x')::ren) t t'.
Proof.
  intros.
  induction H1.
  - constructor.
    constructor.
    + simpl in H. auto.
    + simpl in H0. auto.
    + auto.
  - constructor.
    eapply alpha_swap with (ren := ((x, x')::(x0, y)::sigma)).
    + constructor.
      * simpl in H. auto.
      * simpl in H0. auto.
      * apply legalRenSwap_id.
    + apply IHAlpha.
      apply not_tv_dc_lam in H. auto.
      apply not_tv_dc_lam in H0. auto.
  - constructor.
    + apply IHAlpha1; auto. 
      apply not_tv_dc_appl in H. auto.
      apply not_tv_dc_appl in H0. auto.
    + apply IHAlpha2; auto.
      apply not_tv_dc_appr in H. auto.
      apply not_tv_dc_appr in H0. auto.
  - constructor.
Qed.

  (* 

It feels weird to have these ones here, but they use constructions, so they have to!

  Idea: move to some GU term that has no problematic bniders
  Alpha ren (to_GU_ x [] t) (to_GU_ x [] t')  
  ->  Alpha ((x, x')::ren) (to_GU_ x t) (to_GU_ x t')
  
  Idea works perfectly! Thanks brain :).
  *)
Lemma alpha_extend_fresh {x x' ren t t'}:
  ~ In x (ftv t) ->
  ~ In x' (ftv t') ->
  Alpha ren t t' ->  

  Alpha ((x, x')::ren) t t'.
Proof.
  intros H_nxt H_nx't' Ha_t.
  remember (to_GU'' x t) as tgu.
  remember (to_GU'' x' t') as t'gu.
  assert (Alpha ren tgu t'gu) as Ht.
  {
    eapply @alpha_trans with (t := t) (ren := ctx_id_left ren); eauto.
    eapply id_left_trans.
    eapply alpha_extend_ids.
    apply ctx_id_left_is_id.
    subst.
    apply @alpha_sym with (ren := nil); eauto.
    constructor.
    eapply to_GU''__alpha.

    eapply @alpha_trans with (t := t') (ren' := ctx_id_right ren); eauto.
    eapply id_right_trans. eapply alpha_extend_ids. apply ctx_id_right_is_id.
    subst.
    eapply to_GU''__alpha.
  }
  assert (~ In x (tv tgu)).
  {
    apply not_ftv_btv_then_not_tv; auto.
    - subst.
      eapply alpha_preserves_no_ftv.
      exact H_nxt.
      eapply to_GU''__alpha.
      constructor.
    - subst.
      apply to_GU''__btv.
  }
  assert (~ In x' (tv t'gu)).
  {
    apply not_ftv_btv_then_not_tv; auto.
    - subst.
      eapply alpha_preserves_no_ftv.
      exact H_nx't'.
      eapply to_GU''__alpha.
      constructor.
    - subst.
      apply to_GU''__btv.
  }

  assert (Alpha ((x, x')::ren) tgu t'gu).
  {
    apply alpha_extend_fresh_tv; auto.

  }

  eapply @alpha_trans with (t := tgu) (ren := (ctx_id_left ((x, x')::ren))).
  eapply id_left_trans. eapply alpha_extend_ids. apply ctx_id_left_is_id.
  subst.
  eapply to_GU''__alpha.

  eapply @alpha_trans with (t := t'gu) (ren' := (ctx_id_right ((x, x')::ren))); eauto.
  eapply id_right_trans. eapply alpha_extend_ids. apply ctx_id_right_is_id.
  subst.
  eapply @alpha_sym with (ren := nil); eauto. constructor.
  eapply to_GU''__alpha.
Qed.

  (*

  We know alphaSubs ren sigma sigma'.
  g2 and g3 are both fresh over sigma and sigma', so no issue.

  But what if g2 and g3 not fresh over ren?

  well, let's look at a simpler case where sigma = [Z := t] and sigma' = [Z' := t']
  Suppose now g2 in ren. We have alphaSubs ren sigma sigma'. Since g2 not in Z or t, we cannot have that there is a (g2, B) term with B in Z or t.
  Hence it is a vacuous one, and we can remove it.
  Do this for every g2 or g3 and we are left with a ren that does not contain any g2 or g3.
  Now we can add it and it does nott break shadowing :)
*)
Lemma alpha_ctx_ren_extend_fresh_ftv sigma sigma' x x' ren:
  ~ In x (ftv_keys_env sigma) ->
  ~ In x' (ftv_keys_env sigma') ->
  alphaSubs ren sigma sigma' ->
  alphaSubs ((x, x')::ren) sigma sigma'.
Proof.
  intros H_nxσ H_nx'σ' H_α.
  induction H_α.
  - constructor.
  - constructor.
    + apply IHH_α. auto. simpl in H_nxσ. 
      * apply de_morgan2 in H_nxσ. destruct H_nxσ as [_ H_nxσ].
        apply not_in_app in H_nxσ as [_ H_nxσ]. auto.
      * apply de_morgan2 in H_nx'σ'. destruct H_nx'σ' as [_ H_nx'σ'].
        apply not_in_app in H_nx'σ' as [_ H_nx'σ']. auto.
    + constructor; auto.
      * apply de_morgan2 in H_nxσ as [H_nxσ _]; auto.
      * apply de_morgan2 in H_nx'σ' as [H_nx'σ' _]; auto.
    + apply alpha_extend_fresh; auto.
      * apply de_morgan2 in H_nxσ. destruct H_nxσ as [_ H_nxσ].
        apply not_in_app in H_nxσ as [H_nxσ _]. auto.
      * apply de_morgan2 in H_nx'σ'. destruct H_nx'σ' as [_ H_nx'σ'].
        apply not_in_app in H_nx'σ' as [H_nx'σ' _]. auto.
Qed.


(* Since we have Alpha ren s s, we know no ftv in s is in ren! (or it is identity, so we already no that we won't get breaking
  and if we do it is with variables that do not do antying to s
)*)
Lemma alpha_extend_id'' {s z ren}:
  Alpha ren s s -> Alpha ((z, z)::ren ) s s.
Proof.
  destruct (in_dec string_dec z (ftv s)).
  - intros.

    (* By contradiction: If z breaks shadowing in ren, then there is a (z, z') in there with z' <> z. 
    Then not ren ⊢ s ~ s*)
    assert (NotBreakShadowing z ren).
    {
      dependent induction H.
      - apply ftv_var in i; subst.
        induction sigma.
        + constructor.
        + destruct a0 as [a1 a2].
          inversion a; subst.
          * apply not_break_shadow_id.
          * apply not_break_shadow_cons; auto.
      - 
         assert (z <> x).
        {
          apply ftv_lam_in_no_binder in i. auto.
        }
        assert (Hs1_refl: s1 = s1) by auto.
        specialize (IHAlpha (ftv_lam_helper i) Hs1_refl).
        inversion IHAlpha; subst.
        + auto.
        + contradiction.
      - simpl in i. 
        apply in_prop_to_set in i.
        apply in_app_or_set in i.
        destruct i.
        + apply in_set_to_prop in i. apply IHAlpha1; auto.
        + apply in_set_to_prop in i. apply IHAlpha2; auto.
      - inversion i.
    }
    intros.
    eapply alpha_extend_id'; auto.
  - intros.
    apply alpha_extend_vacuous_ftv; eauto.
Qed.
