From PlutusCert Require Import
  STLC
  Alpha.alpha.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma alpha_exampl x y y' A :
  x <> y -> y <> y' -> x <> y' ->
  Alpha [] (@tmabs Lam x A (@tmabs Lam y A (@tmbin App (tmvar x) (tmvar y)))) (@tmabs Lam y A (@tmabs Lam y' A (@tmbin App (tmvar y) (tmvar y')))).
Proof.
  intros Hxy Hyy' Hxy'.
  apply alpha_lam.
  apply alpha_lam.
  apply alpha_app.
  - apply alpha_var. apply alpha_var_diff; try symmetry; try assumption.
    apply alpha_var_cons; reflexivity.
  - apply alpha_var. apply alpha_var_cons; reflexivity.
Qed.

(* Showcasing shadowing behaviour is right *)
Lemma alpha_counterexample x y z A :
  x <> y -> x <> z -> y <> z ->
  (Alpha [] (@tmabs Lam x A (@tmabs Lam y A (@tmbin App (tmvar x) (tmvar y))))
    (@tmabs Lam z A (@tmabs Lam z A (@tmbin App (tmvar z) (tmvar z)))) -> False).
Proof.
  intros Hxy Hxz Hyz Halpha.
  inversion Halpha; subst.
  inversion H1; subst.
  inversion H2; subst.
  inversion H4; subst.
  inversion H5; subst.
  - contradiction Hxy. subst. reflexivity.
  - contradiction.
Qed.
