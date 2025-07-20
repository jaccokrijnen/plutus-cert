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
  construct_GU_R
  construct_GU
  psubs
  alpha_vacuous
  step_naive
  util
  STLC GU_NC
  Alpha.alpha
  variables
  alpha_subs
  alpha_freshness.

Require Import Coq.Program.Equality.

(* Renaming the name that we substitute. *)
(* We need a legal ren swap because the new binders get in front of the (x, y) in the inductive step of the lambda*)
Lemma alpha_rename_binder_stronger x y s t t' : forall Rt s' Rs,
  Alpha Rs s s' ->
  Alpha Rt t t' ->
  LegalRenSwaps ((x, y)::Rt) Rs ->
  NC s [(x, t)] ->
  NC s' [(y, t')] ->
  Alpha Rt (sub x t s) (sub y t' s').
Proof with eauto with gu_nc_db.
  intros.
  generalize dependent Rt.
  generalize dependent Rs.
  generalize dependent t.
  generalize dependent t'.
  generalize dependent s'.
  induction s; intros; inversion H; subst; simpl.
  - destr_eqb_eq x s; destr_eqb_eq y y0; eauto.
    + exfalso.
      apply lrss_sym in H1.
      apply (alpha_swaps H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H10; auto.
    + exfalso.
      apply lrss_sym in H1.
      apply (alpha_swaps H1) in H.
      inversion H; subst.
      inversion H9; subst.
      contradiction H4; auto.
      contradiction H13; auto.
    + eapply @alpha_swaps with (R1 := ((x, y)::Rt)) in H.
      inversion H; subst.
      inversion H10; subst; try contradiction.
      apply alpha_var.
      assumption.
      apply lrss_sym. auto.
  - constructor.
    eapply IHs; eauto...
    + eapply alpha_extend_vacuous_ftv.
      * apply nc_ftv_env with (x := s) in H2.
        simpl in H2.
        intuition. apply btv_lam.
      * apply nc_ftv_env with (x := y0) in H3.
        simpl in H3.
        intuition. apply btv_lam.
      * assumption.
    + eapply @lrss_trans with (R2 := ((s, y0)::(x, y)::Rt)).
      * eapply starSE.
        -- apply starR.
        --
          ++ constructor.
            ** apply nc_ftv_env with (x := s) in H2.
              simpl in H2. intuition. apply btv_lam.
            ** apply nc_ftv_env with (x := y0) in H3.
              simpl in H3. intuition. apply btv_lam.
            ** apply lrs_id.
      * apply lrss_cons. auto.
  - constructor; eauto with gu_nc_db.
  - constructor.
Qed.



(* Parallel substitutions preserve α-equivalence *)
Lemma psubs__α s : forall R s' sigma sigma',
  NC s sigma ->
  NC s' sigma' ->
  Alpha R s s' ->
  AlphaSubs R sigma sigma' ->
  Alpha R (psubs sigma s) (psubs sigma' s').
Proof with eauto with gu_nc_db.
  induction s; intros; inv H1; simpl.
  all: try constructor...
  - destruct (lookup s sigma) eqn:Hl_x_σ.
    + destruct (AlphaSubs_right_ex H2 H5 Hl_x_σ) as [t' [Hl_x_σ' Ht'_a] ].
      now rewrite Hl_x_σ'.
    + rewrite (AlphaSubs_right_nex H2 H5 Hl_x_σ).
      constructor. assumption.
  - eapply IHs...
    * eapply AlphaSubs_extend_fresh; auto;
      eapply nc_ftv_env; eauto; apply btv_lam.
Qed.





(* Commutativity of substitutions. *)
(* Intuitively:
  [x := σ(t)] σ(s)  =   σ([x := t] s)
*)
Lemma commute_sub_naive R x s t (sigma sigma' : list (string * term)) xtsAlpha:
  Alpha R (sub x t s) xtsAlpha ->
  AlphaSubs R sigma sigma' ->

  (* these two just say: x not in key or ftv sigma*)
  ~ In x (map fst sigma) -> (* Hx_key *)
  (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) -> (* Hx_values*)
  NC xtsAlpha sigma' ->
  NC s [(x, t)] ->
  NC s sigma ->
  NC t sigma ->
  NC (psubs sigma s) [(x, psubs sigma t)] ->
  Alpha R (sub x (psubs sigma t) (psubs sigma s))
      (psubs sigma' xtsAlpha).
Proof with eauto with gu_nc_db.
  intros Ha_sub Hctx_σ Hx_key Hx_value HNC_sub HNC_s_x HNC_s_σ HNC_t_σ HNC_subs.
  generalize dependent xtsAlpha.
  generalize dependent R.
  induction s; intros.
  - (* Here we need to have that x does not occur in lhs or rhs of sigma! *)
    destr_eqb_eq x s.
    + simpl in Ha_sub. rewrite String.eqb_refl in Ha_sub.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * contradiction.   (* Uses Hx_key*)
      * assert (Hsub_vac: psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var.
        rewrite Hsub_vac.
        simpl.
        rewrite String.eqb_refl.
        eapply psubs__α; eauto.
    + simpl in Ha_sub.
      rewrite <- String.eqb_neq in H.
      rewrite H in Ha_sub.
      inversion Ha_sub; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * rewrite sub_vac; auto.
        {
          eapply psubs__α; eauto.
        }
        apply psubs_no_ftv.
        -- apply ftv_keys_env_helper; auto. (* uses Hx_values *)
        -- apply String.eqb_neq. assumption.
        -- intros Hcontra.
           apply nc_ftv_env with (x := x) in HNC_subs; eauto.
           apply ftv_keys_env__no_keys in HNC_subs; eauto.
           simpl in HNC_subs. intuition.
      * assert (Hsub_vac: psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var.
        rewrite Hsub_vac.
        unfold sub.
        rewrite H.
        rewrite <- Hsub_vac.
        eapply psubs__α; eauto.

  - inversion Ha_sub; subst.
    constructor.
    eapply IHs; try eapply nc_lam; eauto.
    apply AlphaSubs_extend_fresh; eauto.
    + eapply nc_ftv_env in HNC_s_σ; eauto. apply btv_lam.
    + eapply nc_ftv_env in HNC_sub; eauto. apply btv_lam.
  - simpl in Ha_sub.
    inversion Ha_sub; subst.
    constructor. fold sub.
    + eapply IHs1...
    + eapply IHs2...
  - simpl.
    simpl in Ha_sub.
    inversion Ha_sub.
    simpl.
    constructor.
Qed.
