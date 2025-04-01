Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
From PlutusCert Require Import STLC_named alpha.alpha Util.List util freshness.

(* One subsitution is related to the other through the alpha context*)
Inductive αCtxSub : list (string * string) -> list (string * term) -> list (string * term) -> Set :=
  | alpha_ctx_nil R : αCtxSub R [] []
  | alpha_ctx_cons R σ σ' x y t t' :
  (* TODO: what about sigma and sigma'? no conditions?*)
    αCtxSub R σ σ' ->
    AlphaVar R x y ->
    Alpha R t t' ->
    αCtxSub R ((x, t)::σ) ((y, t')::σ').


Lemma alpha_ctx_found ren sigma sigma' x x' t t' :
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = Some t ->
  lookup x' sigma' = Some t' ->
  Alpha ren t t'.
Proof.
Admitted.

Lemma alpha_ctx_left_ex {ren sigma sigma' x x' t' }:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x' sigma' = Some t' ->
  { t & prod (lookup x sigma = Some t) (Alpha ren t t')}.
Proof.
Admitted.

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

Lemma alpha_ctx_left_nex {ren sigma sigma' x x'}:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x' sigma' = None ->
  lookup x sigma = None.
Admitted.

Lemma alpha_ctx_right_nex {ren sigma sigma' x x'}:
  αCtxSub ren sigma sigma' ->
  AlphaVar ren x x' ->
  lookup x sigma = None ->
  lookup x' sigma' = None.
Admitted.

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





Fixpoint ftv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (ftv t) ++ (ftv_keys_env sigma')
  end.


Require Import Coq.Program.Equality.

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

Lemma αctx_ids idCtx σ σ' :
  IdCtx idCtx -> αCtxSub nil σ σ' -> αCtxSub idCtx σ σ'.
Admitted.

Lemma extend_ftv_keys_env_to_tv x sigma :
  In x (ftv_keys_env sigma) -> In x (tv_keys_env sigma).
Proof.
Admitted.