Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
From PlutusCert Require Import STLC Alpha.alpha Util.List util variables.
Require Import Coq.Program.Equality.
Require Import ssreflect.

(* One subsitution is related to the other through the alpha context*)
Inductive AlphaSubs : list (string * string) -> list (string * term) -> list (string * term) -> Set :=
  | AlphaSubs_nil R : AlphaSubs R [] []
  | AlphaSubs_cons R σ σ' x y t t' :
    AlphaSubs R σ σ' ->
    AlphaVar R x y ->
    Alpha R t t' ->
    AlphaSubs R ((x, t)::σ) ((y, t')::σ').

(* Symmetry of α-equivalent substitutions*)
Lemma AlphaSubs_sym σ σ' R :
  AlphaSubs R σ σ' -> AlphaSubs (sym_alpha_ctx R) σ' σ.
Proof.
  intros Hctx.
  induction Hctx.
  all: constructor; auto.
  - eapply alphavar_sym; eauto. apply sym_alpha_ctx_is_sym.
  - eapply alpha_sym; eauto. apply sym_alpha_ctx_is_sym.
Qed.

(* Existence of variables in a substitution σ implies existence in σ': right *)
Lemma AlphaSubs_right_ex {R sigma sigma' x x' t }:
  AlphaSubs R sigma sigma' ->
  AlphaVar R x x' ->
  lookup x sigma = Some t ->
  {t' & prod (lookup x' sigma' = Some t') (Alpha R t t')}.
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
    specialize (IHAlphaSubs Hav_xx' H1) as [t'0 [Hlookup Ha_t]].
    exists t'0. split; auto.
    simpl. rewrite <- String.eqb_neq in H0. rewrite H0. auto.
Qed.

(* Existence of variables in a substitution σ implies existence in σ': left *)
Lemma AlphaSubs_left_ex {R sigma sigma' x x' t' }:
  AlphaSubs R sigma sigma' ->
  AlphaVar R x x' ->
  lookup x' sigma' = Some t' ->
  { t & prod (lookup x sigma = Some t) (Alpha R t t')}.
Proof.
  intros Hctx HA_x Hl.
  eapply @alphavar_sym with (R' := sym_alpha_ctx R) in HA_x; auto.
  2: { apply sym_alpha_ctx_is_sym. }
  apply @AlphaSubs_sym with (R := R) in Hctx; auto.
  eapply AlphaSubs_right_ex in Hl as [t'' [Hl_t'' Ha_t']]; eauto.
  exists t''. split; auto.
  eapply @alpha_sym with (R := (sym_alpha_ctx R)); auto.
  apply sym_alpha_ctx_left_is_sym.
Qed.

(* Inexistence of variables in a substitution σ implies inexistence in σ': left *)
Lemma AlphaSubs_left_nex {R sigma sigma' x x'}:
  AlphaSubs R sigma sigma' ->
  AlphaVar R x x' ->
  lookup x' sigma' = None ->
  lookup x sigma = None.
Proof.
  intros Hctx HA_x Hl.
  apply not_in__lookup.
  intros Hcontra.
  apply in_map_iff in Hcontra as [ [x'' t] [Hlookup Hcontra'] ].
  apply in_map__exists_lookup in Hcontra' as [t' Hl_t'].
  simpl in Hlookup. subst.
  eapply (AlphaSubs_right_ex Hctx HA_x) in Hl_t' as [t'0 [Hl_t'0 Ha_t'0]].
  congruence.
Qed.

(* Inexistence of variables in a substitution σ implies inexistence in σ': right *)
Lemma AlphaSubs_right_nex {R sigma sigma' x x'}:
  AlphaSubs R sigma sigma' ->
  AlphaVar R x x' ->
  lookup x sigma = None ->
  lookup x' sigma' = None.
Proof.
  intros Hctx HA_x Hl.
  apply not_in__lookup.
  intros Hcontra.
  apply in_map_iff in Hcontra as [ [x'' t] [Hlookup Hcontra'] ].
  apply in_map__exists_lookup in Hcontra' as [t' Hl_t'].
  simpl in Hlookup. subst.
  eapply (AlphaSubs_left_ex Hctx HA_x) in Hl_t' as [t'0 [Hl_t'0 Ha_t'0]].
  congruence.
Qed.

(* Syntactically identical substitutions are α-equivalent in an empty renaming context*)
Lemma AlphaSubs_R_nil {sigma }:
  AlphaSubs [] sigma sigma.
Proof.
  induction sigma.
  - apply AlphaSubs_nil.
  - destruct a.
    apply AlphaSubs_cons; auto.
    + apply alpha_var_refl.
    + apply alpha_refl. apply id_ctx_nil.
Qed.

(* Transitivity of α-equivalent substitutions*)
Lemma AlphaSubs_trans R1 R2 R σ σ' σ'' :
  αCtxTrans R1 R2 R -> 
  AlphaSubs R1 σ σ' -> AlphaSubs R2 σ' σ'' -> AlphaSubs R σ σ''.
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

(* Extension of identiy renamings on the right of an existing context is always allowed*)
Lemma AlphaSubs_sub_extend_ids_right σ σ' R1 R2 :
  IdCtx R2 -> AlphaSubs R1 σ σ' -> AlphaSubs (R1 ++ R2) σ σ'.
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
