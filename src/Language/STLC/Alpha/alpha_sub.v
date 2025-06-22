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

From PlutusCert Require Import construct_GU_R construct_GU psubs alpha_vacuous construct_GU step_naive psubs util STLC GU_NC_BU Alpha.alpha variables util alpha_ctx_sub alpha_freshness.

Require Import Coq.Program.Equality.

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
    + eapply @alpha_swaps with (ren' := ((x, y)::Rt)) in H.
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
    + eapply @lrss_trans with (ren2 := ((s, y0)::(x, y)::Rt)).
      * eapply starSE.
        -- apply starR.
        -- 
          ++ constructor. 
            ** apply nc_ftv_env with (x := s) in H2.
              simpl in H2. intuition. apply btv_lam.
            ** apply nc_ftv_env with (x := y0) in H3.
              simpl in H3. intuition. apply btv_lam.
            ** apply legalRenSwap_id.
      * apply lrss_cons. auto.
  - constructor; eauto with gu_nc_db.
  - constructor.
Qed.



(* May also work on sequential substiutions with additional assumptions.
  For now only needed for parallel substitutions
*)
Lemma psubs__α s : forall R s' sigma sigma',
  NC s sigma ->
  NC s' sigma' ->
  Alpha R s s' ->
  αCtxSub R sigma sigma' ->
  Alpha R (psubs sigma s) (psubs sigma' s').
Proof with eauto with gu_nc_db.
  induction s; intros; inv H1; simpl.
  all: try constructor...
  - destruct (lookup s sigma) eqn:Hl_x_σ.
    + destruct (alpha_ctx_right_ex H2 H5 Hl_x_σ) as [t' [Hl_x_σ' Ht'_a] ].
      now rewrite Hl_x_σ'.
    + rewrite (alpha_ctx_right_nex H2 H5 Hl_x_σ).
      constructor. assumption.
  - eapply IHs...
    * eapply alpha_ctx_ren_extend_fresh_ftv; auto;
      eapply nc_ftv_env; eauto; apply btv_lam.
Qed.




(* I want to be in a position where the binders are chosen thus that I can do substitueT
  without checking if we are tyring to substitute a binder:
    i.e. no checks in substituteT 
    Then we ahve the property:
    subsT x t (tmabs y T s) = tmabs y T (subsT x t s) even if x = y (because that cannot happen anymore)
      Then also NC can go into the lambda
    this can be put into the NC property?
    *)
  (* Maybe we can leave out the R by switching to a renaming approach? *)

(* TODO: These sigma's can be single substitutions I think!
  - Used in step_subst, there it can be single substs
    - Used in beta_expansion: single substs *)

(*
  [x := σ(t)] σ(s)  =   σ([x := t] s)
*)
Lemma commute_sub_naive R x s t (sigma sigma' : list (string * term)) xtsAlpha:
  Alpha R (sub x t s) xtsAlpha ->
  αCtxSub R sigma sigma' -> (* TODO: Vars in R not in sigma?*)

  (* these two just say: x not in key or ftv sigma*)
  ~ In x (map fst sigma) ->
  (forall ftvs, In ftvs (map snd sigma) -> ~ In x (ftv ftvs)) -> 
  NC xtsAlpha sigma' ->
  NC s [(x, t)] ->
  NC s sigma ->
  NC t sigma ->
  NC (psubs sigma s) [(x, psubs sigma t)] ->
  (* s.t. substituteTs sigma xtsAlpha does not capture 
    e.g. suppose sigma:= [y := x]
    and xtsAlpha = λx. y.
    then substituting would capture.
    But we can always choose an alpha equivalent xtsAlpha with 
    different binder names not occuring in the rhs of sigma
  *)
  R ⊢ (sub x (psubs sigma t) (psubs sigma s))
      ~ (psubs sigma' xtsAlpha).
Proof with eauto with gu_nc_db.
  intros Ha_sub Hctx_σ Hx_key Hx_value HNC_sub HNC_s_x HNC_s_σ HNC_t_σ HNC_subs.
  generalize dependent xtsAlpha.
  generalize dependent R.
  induction s; intros.
  - (* We need to have that x does not occur in lhs or rhs of sigma! We have control over x
    when calling this function, so we should be good.*)
    destr_eqb_eq x s.
    + simpl in Ha_sub. rewrite String.eqb_refl in Ha_sub.
      destruct (in_dec String.string_dec s (map fst sigma)).
      * contradiction. (* Uses Hx_key *)      
      * assert (Hsub_vac: psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var. (* DONE: s not in sigma*)
        rewrite Hsub_vac.
        simpl. 
        rewrite String.eqb_refl.
        eapply psubs__α; eauto.
    + simpl in Ha_sub. 
      rewrite <- String.eqb_neq in H.
      rewrite H in Ha_sub.
      inversion Ha_sub; subst.
      destruct (in_dec String.string_dec s (map fst sigma)).
      (* 
        by s in keys, ther emust be a value. Hmm. But these are sequential substs...
      *)
      * rewrite sub_vac; auto.
        {
          eapply psubs__α; eauto.
        }
        apply psubs_no_ftv.
        -- apply ftv_keys_env_helper; auto. (* uses Hx_value *) 
        -- apply String.eqb_neq. assumption.
        -- intros Hcontra.
           apply nc_ftv_env with (x := x) in HNC_subs; eauto.
           apply ftv_keys_env__no_keys in HNC_subs; eauto.
           simpl in HNC_subs. intuition.
      * assert (Hsub_vac: psubs sigma (tmvar s) = tmvar s) by now apply psubs_vac_var. (* DONE : s not in fst sigma *)
        rewrite Hsub_vac.
        unfold sub.
        rewrite H.
        rewrite <- Hsub_vac.
        eapply psubs__α; eauto.

  - inversion Ha_sub; subst.
    constructor.
    eapply IHs; try eapply nc_lam; eauto.
    apply alpha_ctx_ren_extend_fresh_ftv; eauto.
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
