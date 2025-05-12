
From PlutusCert Require Import STLC_named alpha.alpha alpha_ctx_sub Util.List freshness util alpha_rename.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Program.Equality.

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

Lemma weaken_vacuous_alpha {X X' ren t t'} :
  Alpha ((X, X')::ren) t t' -> ~ In X (ftv t) -> ~ In X' (ftv t') -> Alpha ren t t'.
Proof.
  (* Proof will go something similar to alphaRenameStronger *)
Admitted.

Lemma alpha_preserves_ftv' {x s s' ren} :
  In x (ftv s) -> Alpha ren s s' -> { x' & prod (AlphaVar ren x x') (In x' (ftv s')) }.
Proof.
  intros Hxins Halphas.
  induction Halphas.
  - apply ftv_var in Hxins; subst.
    exists y; split; auto.
    apply ftv_var_eq.
  - assert (x <> x0).
    {
      intros Hcontra; subst.
      apply ftv_lam_no_binder in Hxins.
      contradiction.
    } 
    apply ftv_lam_helper in Hxins.
    destruct (IHHalphas Hxins) as [x' [Halphax Hx'ins'] ].
    exists x'; split.
    + inversion Halphax; subst; try contradiction. assumption.
    + simpl.
      apply in_in_remove; auto.
      assert (x' <> y).
      {
        intros Hcontra; subst.
        inversion Halphax; subst; contradiction.
      }
      assumption.
  - simpl in Hxins; apply in_app_sum in Hxins; destruct Hxins as [H | H].
    + destruct (IHHalphas1 H) as [x' [Halphax Hx'ins'] ].
      exists x'; split; auto.
      apply in_or_app; left; auto.
    + destruct (IHHalphas2 H) as [x' [Halphax Hx'ins'] ].
      exists x'; split; auto.
      apply in_or_app; right; auto.
  - inversion Hxins.
Qed.

Lemma alpha_preserves_ftv {x x' s s' ren } :
  In x (ftv s) ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  In x' (ftv s').
Proof.
  intros Hxins Halphas Halphax.
  apply (alpha_preserves_ftv' Hxins) in Halphas as [y [Halphay Hyins] ].
  apply (alphavar_unique_right Halphax) in Halphay; subst.
  assumption.
Qed.

Lemma alpha_preserves_no_ftv {x x' s s' ren} :
  ~ In x (ftv s) ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  ~ In x' (ftv s').
Proof.
  intros Hnotin Halphas Halphax.
  intros Hcontra.
  assert (sym_alpha_ctx ren ⊢ s' ~ s).
  {
    eapply alpha_sym; eauto.
    apply sym_alpha_ctx_is_sym.
  }
  assert (AlphaVar (sym_alpha_ctx ren) x' x).
  {
    eapply alphavar_sym; eauto.
    apply sym_alpha_ctx_is_sym.
  }
  eapply (alpha_preserves_ftv Hcontra H) in H0.
  contradiction.
Qed.

(* Uses stronger assumption that x notin tv s instead of ftv s
  Makes life easier for not having to deal with binders 
  Example: x notin ftv (tmlam x. x), but x in ftv x, which is its body.
          However x in tv (tmlam x. x), as well as in tmlam x. y. easier.
   *)
Lemma alpha_preserves_ftv_from_tv {x x' s s' ren} :
  ~ In x (tv s) ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  ~ In x' (ftv s').
Proof.
  intros.
  eapply alpha_preserves_no_ftv; eauto.
  intros Hcontra.
  apply extend_ftv_to_tv in Hcontra.
  contradiction.
Qed.

Lemma alpha_preserves_ftv_tv_right {x x' s s' ren} :
  ~ In x' (tv s') ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  ~ In x (ftv s).
Proof.
  intros.
  eapply alpha_preserves_no_ftv; eauto.
  - intros Hcontra.
    apply extend_ftv_to_tv in Hcontra.
    now apply H in Hcontra.
  - eapply alpha_sym.
    + apply sym_alpha_ctx_is_sym.
    + eauto.
  - eapply alphavar_sym; eauto.
    apply sym_alpha_ctx_is_sym.
Qed.