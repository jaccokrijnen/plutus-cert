
From PlutusCert Require Import 
  STLC
  Alpha.alpha
  Util.List 
  variables 
  util. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Program.Equality.

(* Strengthened statement of alpha_preserves_ftv *)
Lemma alpha_preserves_ftv' {x s s' R} :
  In x (ftv s) -> Alpha R s s' -> { x' & prod (AlphaVar R x x') (In x' (ftv s')) }.
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

(* Free type variables are preserved by and up to alpha equivalence *)
Lemma alpha_preserves_ftv {x x' s s' R } :
  In x (ftv s) ->
  Alpha R s s' ->
  AlphaVar R x x' ->
  In x' (ftv s').
Proof.
  intros Hxins Halphas Halphax.
  apply (alpha_preserves_ftv' Hxins) in Halphas as [y [Halphay Hyins] ].
  apply (alphavar_unique_right Halphax) in Halphay; subst.
  assumption.
Qed.

(* Not occuring free is also preserved under alpha equivalence*)
Lemma alpha_preserves_no_ftv {x x' s s' R} :
  ~ In x (ftv s) ->
  Alpha R s s' ->
  AlphaVar R x x' ->
  ~ In x' (ftv s').
Proof.
  intros Hnotin Halphas Halphax.
  intros Hcontra.
  assert (Alpha (sym_alpha_ctx R) s' s).
  {
    eapply alpha_sym; eauto.
    apply sym_alpha_ctx_is_sym.
  }
  assert (AlphaVar (sym_alpha_ctx R) x' x).
  {
    eapply alphavar_sym; eauto.
    apply sym_alpha_ctx_is_sym.
  }
  eapply (alpha_preserves_ftv Hcontra H) in H0.
  contradiction.
Qed.

