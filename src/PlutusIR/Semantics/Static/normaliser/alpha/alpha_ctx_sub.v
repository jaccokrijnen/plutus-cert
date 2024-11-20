Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
From PlutusCert Require Import STLC_named alpha Util.List.

(* One subsitution is related to the other through the alpha context*)
Inductive αCtxSub : list (string * string) -> list (string * term) -> list (string * term) -> Prop :=
  | alpha_ctx_nil : αCtxSub [] [] []
  | alpha_ctx_cons ren sigma sigma' x y t t' :
    AlphaVar ren x y ->
    Alpha ren t t' ->
    αCtxSub ren ((x, t)::sigma) ((y, t')::sigma').

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
Admitted.

Lemma alpha_ctx_ren_nil {sigma }:
  αCtxSub [] sigma sigma.
Proof.
  induction sigma.
  - apply alpha_ctx_nil.
  - destruct a.
    apply alpha_ctx_cons.
    + apply alpha_var_refl.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.

  (*

  We know αCtxSub ren sigma sigma'.
  g2 and g3 are both fresh over sigma and sigma', so no issue.

  But what if g2 and g3 not fresh over ren?

  well, let's look at a simpler case where sigma = [Z := t] and sigma' = [Z' := t']
  Suppose now g2 in ren. We have αCtxSub ren sigma sigma'. Since g2 not in Z or t, we cannot have that there is a (g2, B) term with B in Z or t.
  Hence it is a vacuous one, and we can remove it.
  Do this for every g2 or g3 and we are left with a ren that does not contain any g2 or g3.
  Now we can add it and it does nott break shadowing :)
*)
Lemma alpha_ctx_ren_extend_fresh sigma sigma' x x' ren:
  ~ In x (tv_keys_env sigma) ->
  ~ In x' (tv_keys_env sigma') ->
  αCtxSub ren sigma sigma' ->
  αCtxSub ((x, x')::ren) sigma sigma'.
Admitted.

(* TODO: SUPERSEDED BY alpha_ctx_ren_extend_fresh. The statements are almost identical (with respect to what we use them for) *)
(* TODO: t and t' are totall unrelevant here, how do I make them placeholders or something? *)
Lemma extend_alpha_ctx_fresh {x x' sigma sigma' sigma_ sigma_' ren t t'}:
  x = fresh2 (sigma_ ++ sigma) t ->
  x' = fresh2 (sigma_' ++ sigma') t' ->
  αCtxSub ren sigma sigma' ->
  αCtxSub ((x, x')::ren) sigma sigma'.
Admitted.