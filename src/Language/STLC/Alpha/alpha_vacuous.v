
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
Require Import Coq.Program.Equality.

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

(* If x is not free in s, we can construct an α-equivalent representative that also does not have x as binder *)
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

(* We can append a vacuous renaming: it doesn't do anything by the ~ftv premises*)
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

(* Appending multiple vacuous renamings *)
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

(* Appending multiple vacuous renaming to α-equivalence of substitutions *)
Lemma AlphaSubs_vacuous_R R σ σ' :
  (forall x, In x (map fst R) -> (~ In x (ftv_keys_env σ))) -> (forall x', In x' (map snd R) -> ~ In x' (ftv_keys_env σ')) -> AlphaSubs [] σ σ' -> AlphaSubs R σ σ'.
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

(* The freshness premises make this a vacuous additional renaming*)
Lemma AlphaSubs_extend_fresh sigma sigma' x x' R:
  ~ In x (ftv_keys_env sigma) ->
  ~ In x' (ftv_keys_env sigma') ->
  AlphaSubs R sigma sigma' ->
  AlphaSubs ((x, x')::R) sigma sigma'.
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
    + apply alpha_extend_vacuous_ftv; auto.
      * apply de_morgan2 in H_nxσ. destruct H_nxσ as [_ H_nxσ].
        apply not_in_app in H_nxσ as [H_nxσ _]. auto.
      * apply de_morgan2 in H_nx'σ'. destruct H_nx'σ' as [_ H_nx'σ'].
        apply not_in_app in H_nx'σ' as [H_nx'σ' _]. auto.
Qed.

(* Extending with identity is allowed if we relate identical terms: then R only contains vacuous and identity renamings *)
Lemma alpha_extend_id__refl {s z R}:
  Alpha R s s -> Alpha ((z, z)::R ) s s.
Proof.
  destruct (in_dec string_dec z (ftv s)).
  - intros.

    (* By contradiction: If z breaks shadowing in R, then there is a (z, z') in there with z' <> z.
    Then not R ⊢ s ~ s*)
    assert (NotBreakShadowing z R).
    {
      dependent induction H.
      - apply ftv_var in i; subst.
        induction R.
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
    eapply alpha_extend_id; auto.
  - intros.
    apply alpha_extend_vacuous_ftv; eauto.
Qed.
