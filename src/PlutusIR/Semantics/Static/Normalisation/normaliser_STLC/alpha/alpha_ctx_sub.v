Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
From PlutusCert Require Import STLC_named alpha.alpha Util.List util freshness.
Require Import Coq.Program.Equality.
Require Import ssreflect.

(* One subsitution is related to the other through the alpha context*)
Inductive αCtxSub : list (string * string) -> list (string * term) -> list (string * term) -> Set :=
  | alpha_ctx_nil R : αCtxSub R [] []
  | alpha_ctx_cons R σ σ' x y t t' :
  (* TODO: what about sigma and sigma'? no conditions?*)
    αCtxSub R σ σ' ->
    AlphaVar R x y ->
    Alpha R t t' ->
    αCtxSub R ((x, t)::σ) ((y, t')::σ').


Lemma αctx_sym σ σ' R :
  αCtxSub R σ σ' -> αCtxSub (sym_alpha_ctx R) σ' σ.
Proof.
  intros Hctx.
  induction Hctx.
  all: constructor; auto.
  - eapply alphavar_sym; eauto. apply sym_alpha_ctx_is_sym.
  - eapply alpha_sym; eauto. apply sym_alpha_ctx_is_sym.
Qed.

(* 
(* Not used? *)
Lemma alpha_ctx_found ren sigma sigma' x x' t t' :
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = Some t ->
  lookup x' sigma' = Some t' ->
  Alpha ren t t'.
Proof.
Admitted. *)

Lemma alpha_ctx_right_ex {ren sigma sigma' x x' t }:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = Some t ->
  {t' & prod (lookup x' sigma' = Some t') (Alpha ren t t')}.
Proof.
  intros.
  induction H; try inversion H1.
  destr_eqb_eq x0 x.
  - inversion H3. subst. clear H3.
    apply (alphavar_unique_right a) in H0. subst.
    exists t'. split; auto.
    simpl. rewrite String.eqb_refl. auto.
  - remember H0 as Hav_xx'; clear HeqHav_xx'.
    apply (alphavar_unique_not_left H2 a) in H0.
    simpl in H1. rewrite <- String.eqb_neq in H2. rewrite H2 in H1.
    specialize (IHαCtxSub Hav_xx' H1) as [t'0 [Hlookup Ha_t]].
    exists t'0. split; auto.
    simpl. rewrite <- String.eqb_neq in H0. rewrite H0. auto.
Qed.

Lemma alpha_ctx_left_ex {ren sigma sigma' x x' t' }:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x' sigma' = Some t' ->
  { t & prod (lookup x sigma = Some t) (Alpha ren t t')}.
Proof.
  intros Hctx HA_x Hl.
  eapply @alphavar_sym with (ren' := sym_alpha_ctx ren) in HA_x; auto.
  2: { apply sym_alpha_ctx_is_sym. }
  apply @αctx_sym with (R := ren) in Hctx; auto.
  eapply alpha_ctx_right_ex in Hl as [t'' [Hl_t'' Ha_t']]; eauto.
  exists t''. split; auto.
  eapply @alpha_sym with (ren := (sym_alpha_ctx ren)); auto.
  apply sym_alpha_ctx_left_is_sym.
Qed.

Lemma alpha_ctx_left_nex {ren sigma sigma' x x'}:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x' sigma' = None ->
  lookup x sigma = None.
Proof.
  intros Hctx HA_x Hl.
  apply not_in__lookup.
  intros Hcontra.
  apply in_map_iff in Hcontra as [ [x'' t] [Hlookup Hcontra'] ].
  apply in_map__exists_lookup in Hcontra' as [t' Hl_t'].
  simpl in Hlookup. subst.
  eapply (alpha_ctx_right_ex Hctx HA_x) in Hl_t' as [t'0 [Hl_t'0 Ha_t'0]].
  congruence.
Qed.

Lemma alpha_ctx_right_nex {ren sigma sigma' x x'}:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = None ->
  lookup x' sigma' = None.
Proof.
  intros Hctx HA_x Hl.
  apply not_in__lookup.
  intros Hcontra.
  apply in_map_iff in Hcontra as [ [x'' t] [Hlookup Hcontra'] ].
  apply in_map__exists_lookup in Hcontra' as [t' Hl_t'].
  simpl in Hlookup. subst.
  eapply (alpha_ctx_left_ex Hctx HA_x) in Hl_t' as [t'0 [Hl_t'0 Ha_t'0]].
  congruence.
Qed.

Lemma alpha_ctx_ren_nil {sigma }:
  αCtxSub [] sigma sigma.
Proof.
  induction sigma.
  - apply alpha_ctx_nil.
  - destruct a.
    apply alpha_ctx_cons; auto.
    + apply alpha_var_refl.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma αctx_trans R1 R2 R σ σ' σ'' :
  αCtxTrans R1 R2 R -> 
  αCtxSub R1 σ σ' -> αCtxSub R2 σ' σ'' -> αCtxSub R σ σ''.
Proof.
  intros.
  dependent induction σ.
  - inversion H0; subst.
    inversion H1; subst.
    constructor.
  - inversion H0; subst.
    inversion H1; subst.
    constructor.
    + eapply IHσ; eauto.
    + eapply alpha_var_trans; eauto.
    + eapply alpha_trans; eauto.
Qed.

(* Lemma αctx_ids idCtx σ σ' :
  IdCtx idCtx -> αCtxSub nil σ σ' -> αCtxSub idCtx σ σ'.
Admitted. *)

Lemma αctx_sub_extend_ids_right σ σ' R1 R2 :
  IdCtx R2 -> αCtxSub R1 σ σ' -> αCtxSub (R1 ++ R2) σ σ'.
Proof.
  intros HidR2 Ha.
  dependent induction σ.
  - inversion Ha; subst. constructor.
  - inversion Ha; subst.
    constructor.
    + eapply IHσ; eauto.
    + apply alphavar_extend_ids_right; auto.
    + apply alpha_extend_ids_right; auto.
Qed.

Fixpoint ftv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (ftv t) ++ (ftv_keys_env sigma')
  end.