(** * Strong Normalization of System F *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import List AutosubstSsr.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC_named ARS util.

(** **** Capms lemmas *)
Lemma capms_var sigma X t:
  lookup X sigma = Some t -> capms sigma (tmvar X) = t.
Proof. 
  rewrite capms_equation_1. 
  by move ->.
Qed.

Lemma capms_lam X B sigma s :
  capms sigma (tmlam X B s) = 
    tmlam (fresh2 ((X, tmvar X)::sigma) s) B (capms sigma (rename X (fresh2 ((X, tmvar X)::sigma) s) s)).
Proof.
  rewrite capms_equation_2.
  reflexivity.
Qed.

(** **** One-Step Reduction *)

(* Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope. *)

(* Alpha reduction based on Andrej Bauer (Computer Science stack exchange)*)
(* Inductive relation for:

equalVar :: [(Var,Var)] -> Var -> Var -> Bool
equalVar [] x y = (x == y)
equalVar ((x,y):bound) z w = (x == z && y == w) || (x /= z && y /= w && equalVar bound z w)

equal' :: [(Var, Var)] -> Term -> Term -> Bool
equal' bound (Belong x1 y1) (Belong x2 y2) = (equalVar bound x1 x2 && equalVar bound y1 y2)
equal' bound Bot Bot = True
equal' bound (Imply u1 v1) (Imply u2 v2) = equal' bound u1 u2 && equal' bound v1 v2
equal' bound (Forall x u) (Forall y v) = equal' ((x,y):bound) u v
equal' _ _ _ = False

*)
Inductive AlphaVar : list (string * string) -> string -> string -> Set :=
| alpha_var_refl x : AlphaVar [] x x
| alpha_var_cons z w sigma :
    AlphaVar ((z, w) :: sigma) z w
| alpha_var_diff x y z w sigma :
    x <> z -> 
    y <> w -> 
    AlphaVar sigma z w -> 
    AlphaVar ((x, y) :: sigma) z w.

Inductive Alpha : list (string * string) -> term -> term -> Set :=
| alpha_var x y sigma : 
    AlphaVar sigma x y -> 
    Alpha sigma (tmvar x) (tmvar y)
| alpha_lam x y A s1 s2 sigma :
    Alpha ((x, y) :: sigma) s1 s2 -> 
    Alpha sigma (tmlam x A s1) (tmlam y A s2)
| alpha_app s1 s2 t1 t2 sigma :
    Alpha sigma s1 s2 -> 
    Alpha sigma t1 t2 -> 
    Alpha sigma (tmapp s1 t1) (tmapp s2 t2).

Fixpoint swap (x y : string) (s : term) := 
  match s with
  | tmvar z => if z =? x then tmvar y else if z =? y then tmvar x else tmvar z
  | tmlam z A s' => if z =? x then tmlam y A (swap x y s') else if z =? y then tmlam x A (swap x y s') else tmlam z A (swap x y s')
  | tmapp s1 s2 => tmapp (swap x y s1) (swap x y s2)
  end.

Inductive AlphaSwap : term -> term -> Set :=
| alphaswap_var x :
  AlphaSwap (tmvar x) (tmvar x)
| alphaswap_lam x y A s1 s2 :
  AlphaSwap s1 (swap x y s2) -> 
  AlphaSwap (tmlam x A s1) (tmlam y A s2)
| alphaswap_app s1 s2 t1 t2 :
  AlphaSwap s1 s2 -> 
  AlphaSwap t1 t2 -> 
  AlphaSwap (tmapp s1 t1) (tmapp s2 t2).

(* **** Properties of Alpha *)

(* **** Reflexivity *)

(* **** Examples *)

(* Example of alpha equivalence *)

Notation "sigma '⊢' t1 '~' t2" := (Alpha sigma t1 t2) (at level 40).
(* Notation "t1 '~' t2" := (Alpha [] t1 t2) (at level 40). TODO: This doesnt work, coq doesnt understand when to use which*)

(* **** Properties of Alpha *)

(* **** Reflexivity *)

(* **** Examples *)

(* Example of alpha equivalence *)


(* TODO: Should we add the assumption that we are always substing in fresh stuff? *)
(* TODO: Fresh with respect to what? *)
Fixpoint rename2 (X Y : string) (T : term) : term :=
  match T with
  | tmvar X' => if X =? X' then tmvar Y else tmvar X'
  | tmlam X' K1 T_body => if X =? X' then tmlam X' K1 T_body else tmlam X' K1 (rename2 X Y T_body)
  | tmapp T1 T2 => tmapp (rename2 X Y T1) (rename2 X Y T2)
end.

(* Suppose s1 = x, and s2 = y. Then we have Alpha2 (renameTCA x y s1) s2
    so yes.

    What if s1 = y and s2 = y, then we have Alpha2 (renameTCA x y s1) s2 = Alpha2 y y = True
    But we should not have Alpha2 (tmlam x A y) (tmlam y A y)... so no
*)
Inductive Alpha2 : term -> term -> Set:=
| alpha2_var x :
  Alpha2 (tmvar x) (tmvar x)
| alpha2_app s1 s2 t1 t2 :
  Alpha2 s1 s2 -> 
  Alpha2 t1 t2 -> 
  Alpha2 (tmapp s1 t1) (tmapp s2 t2)
| alpha2_lam x y A s1 s2 :
  Alpha2 (rename2 x y s1) (rename2 y x s2) ->  
  Alpha2 (tmlam x A s1) (tmlam y A s2).

Require Import Ascii.

Inductive Fresh3 : string -> string -> string -> term -> term -> Set :=
| fresh_var fr x y s1 s2 :
    fr <> x -> 
    fr <> y -> 
    ~ In fr (tv s1) ->
    ~ In fr (tv s2) ->
    Fresh3 fr x y s1 s2.

Definition fresh3 (x y : string) (s1 s2 : term) : string :=
  "a" (* new*)
  ++ String.concat EmptyString (
    x :: y :: tv s1 ++ tv s2
  ).

Lemma fresh3_sound_complete :
  forall x y s1 s2, Fresh3 (fresh3 x y s1 s2) x y s1 s2.
Admitted.

(* This is definition 3.1 in https://pdf.sciencedirectassets.com/271538/1-s2.0-S0304397512X00161/1-s2.0-S0304397512000667/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEMH%2F%2F%2F%2F%2F%2F%2F%2F%2F%2FwEaCXVzLWVhc3QtMSJGMEQCIG%2BQqldD%2FjA7NoiWQ8LNNSiVisTNC0Bg6XND41y0KfGFAiAFFmELjxK%2FE%2FcIVfE3L9st4Og6PAdKhLiZyyBDiT8LECq8BQi6%2F%2F%2F%2F%2F%2F%2F%2F%2F%2F8BEAUaDDA1OTAwMzU0Njg2NSIMNeW5gtEinHpeKgTWKpAFBTCfszS77ANhiG%2Fcb%2FsSUt1skJsS%2FXVCRS0jhmCVGks3Yjl622BzjOcdpQYlTVUT2ohNGrxknOvHgVO4%2BcePabv3%2BfAiBGP8s1FOo5%2BH7pBpIhZ7eTKH%2FtvbEP%2BYNUh53QX%2F1wZQQH0oebBlfpTgKtZzii7b2oZI4ibLAOiUfc87x6lDARXz2ROdVZWq6F72kWkcU0cZflFE6hNRcXYiKlcKocu2EvAordoc0XfBhNkOQp%2Fgv%2FtuJeEr130nNMSWdzbRM2AaQ6UQGD8igj5rJJ8z%2FEWIFXQREwtYdiiXi1bJDly5cT7lzyOExLAay8dYV6LPBRRehx5XgaCVqz61z9VPrrWqs1A2zheM22Ryw6ertBj58pIa98jTNbD4STlG1akJV%2BFs2NBr3SDuiDxqEn%2F1FKZz5aOTFfPYjWtppYEZVsjEMtC19mQm8fFIyavO975zFRkJ0IEBWb05i680iC0iOKlhT%2BHLAlDoBmo%2BUje9HHSY5ICQ8LA8avTqPKZOrP%2B4N0CZqscyY0C%2BxSgmD7%2BhVEMFr4EGJv1lWFehonJPheA3Cgd75q4wvAHWa1dUwyXWdnNTr2PVloxTMVTdQswq84QnjDiQe%2FJYu6%2BjrYNSj8vKjfdtUiYbsD2PENBt31gooeo6Jb%2Bf82mh4xHDV6JZ07mTHYwJAkN%2FcjyGFOCRcYYDO4VjftIwnBv1%2BtlaD94BO%2Bxh2HJDbfXWh0ylRRCK9LraPDHTf6ZxnOj0kYsqKyWGO5CID3oyurbhFUowlkaRfyIrxgt%2F89pzVrQtFPryy3dR%2FJbcN4ynvS2hOh2fevptFHV2%2BiD2vM9KRFMbLsz4QgeeO2XzXgwcjXR9KX5UOxg6uu%2FqdtUA%2BCOFrH4wn8S9vAY6sgFY5l2eE1BY7RYQmFsouQcQRDqbBwHdTHBToqQ6Euo6wOOOQdZY5erdrUBAls%2BP5KnQZIDqAVNjbZ34e14BtHVzzDytH6mo3q%2Bg4gUWM5ON0qZy%2BqFuWQKzfnTu7TQisgjYR0OvxABy2D%2FkMSNZ71FEl7EyaWJLuol3EcTd8lyj5G4kBAv487tPpYEZHXczLT3JXPPEgWc96mNnp%2FyUFiQG8F3yy1UpPc5H3d%2BhF%2Bjj%2FlEb&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20250121T094752Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYVUNMHNK4%2F20250121%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=398b562e375d1a16c7f60ab80429dfaf310a35e377e630760503b684f84da28c&hash=3dcb22b98618eeaa6529ad48b4a7b543abf03bc96650448909e29c5712e27c4b&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S0304397512000667&tid=spdf-e832ba5a-7b88-43ab-846d-05556869c86e&sid=48b03c4275472545d69b5e31e4a1d3f9ea1agxrqb&type=client&tsoh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&ua=080b5a51535050500f57&rr=905662a1e825d0b9&cc=nl
Alpha equivalence equalities
Roy L. Crole ∗

We do not swap, but we are working with a fresh variable, so that cannot occur, so then we do not have to swap?
*)
Inductive Alpha3 : term -> term -> Set:=
| alpha3_var x :
  Alpha3 (tmvar x) (tmvar x)
| alpha3_app s1 s2 t1 t2 :
  Alpha3 s1 s2 -> 
  Alpha3 t1 t2 -> 
  Alpha3 (tmapp s1 t1) (tmapp s2 t2)
| alpha3_lam x y A s1 s2 fr :
  Fresh3 fr x y s1 s2 ->
  Alpha3 (rename2 x fr s1) (rename2 y fr s2) ->  
  Alpha3 (tmlam x A s1) (tmlam y A s2).


Inductive Alpha4 : term -> term -> Set:=
| alpha4_var x :
  Alpha4 (tmvar x) (tmvar x)
| alpha4_app s1 s2 t1 t2 :
  Alpha4 s1 s2 -> 
  Alpha4 t1 t2 -> 
  Alpha4 (tmapp s1 t1) (tmapp s2 t2)
| alpha4_lam x A s1 s2 :
  Alpha4 s1 s2 ->
  Alpha4 (tmlam x A s1) (tmlam x A s2)
| alpha4_ren x y A s1 s1' :
  s1' = rename2 x y s1 ->
  Alpha4 (tmlam x A s1) (tmlam y A s1').

(* **** Examples *)

(* Example of alpha equivalence *)


Lemma alpha_exampl x y y' A :
  x <> y -> y <> y' -> x <> y' -> 
  Alpha [] (tmlam x A (tmlam y A (tmapp (tmvar x) (tmvar y)))) (tmlam y A (tmlam y' A (tmapp (tmvar y) (tmvar y')))).
Proof.
  intros Hxy Hyy' Hxy'.
  apply alpha_lam.
  apply alpha_lam.
  apply alpha_app.
  - apply alpha_var. apply alpha_var_diff; try symmetry; try assumption.
    apply alpha_var_cons; reflexivity.
  - apply alpha_var. apply alpha_var_cons; reflexivity.
Qed.

Lemma alpha3_example x y A :
  x <> y ->
  Alpha3 (tmlam x A (tmvar x)) (tmlam y A (tmvar y)).
Proof.
  intros.
  eapply alpha3_lam with (fr := fresh3 x y (tmvar x) (tmvar y)); auto.
  - apply fresh3_sound_complete.
  -
  simpl.
  repeat rewrite String.eqb_refl.
  constructor.
Qed.

Lemma alpha3_example2 x y y' A :
  x <> y -> y <> y' -> x <> y' -> 
  Alpha3 (tmlam x A (tmlam y A (tmapp (tmvar x) (tmvar y)))) (tmlam y A (tmlam y' A (tmapp (tmvar y) (tmvar y')))).
Proof.
  intros.
  econstructor; auto.
  simpl.
  destr_eqb_eq x y; try contradiction.
  apply fresh3_sound_complete.
  simpl.
  rewrite String.eqb_refl.
  destr_eqb_eq y x; try contradiction.
  rewrite String.eqb_refl.
  destr_eqb_eq y y'; try contradiction.
  destr_eqb_eq x y; try contradiction.
  econstructor; auto.
  apply fresh3_sound_complete.
  simpl.
  remember (fresh3 x y _ _) as fr1.
  remember (fresh3 y y' _ _) as fr2.
  assert (y =? fr1 = false) by admit.
  rewrite H5.
  assert (y' =? fr1 = false) by admit; rewrite H6.
  repeat rewrite String.eqb_refl.
  repeat constructor; auto.
Admitted.


Lemma alpha2_exampl x y y' A :
  x <> y -> y <> y' -> x <> y' -> 
  Alpha2 (tmlam x A (tmlam y A (tmapp (tmvar x) (tmvar y)))) (tmlam y A (tmlam y' A (tmapp (tmvar y) (tmvar y')))).
Proof.
  intros Hxy Hyy' Hxy'.
  apply alpha2_lam.
  simpl.
  destr_eqb_eq x y; try contradiction.
  destr_eqb_eq y y'; try contradiction.
  apply alpha2_lam.
  simpl.
  apply alpha2_app.
  repeat rewrite String.eqb_refl.
  simpl.
  rewrite String.eqb_refl.
  destr_eqb_eq y y'; try contradiction.
  destr_eqb_eq y' y; try contradiction.
Abort. (* doesnt work *)


(* Showcasing shadowing behaviour is right *)
Lemma alpha_counterexample x y z A :
  x <> y -> x <> z -> y <> z -> 
  (Alpha [] (tmlam x A (tmlam y A (tmapp (tmvar x) (tmvar y)))) 
    (tmlam z A (tmlam z A (tmapp (tmvar z) (tmvar z)))) -> False).
Proof.
  intros Hxy Hxz Hyz Halpha.
  inversion Halpha; subst.
  inversion H1; subst.
  inversion H2; subst.
  inversion H5; subst.
  inversion H4; subst.
  - contradiction Hxy. reflexivity.
  - contradiction H10. reflexivity.
Qed.

(* Showcasing shadowing behaviour is right *)
Lemma alpha3_counterexample x y z A :
  x <> y -> x <> z -> y <> z -> 
  (Alpha3 (tmlam x A (tmlam y A (tmapp (tmvar x) (tmvar y)))) 
    (tmlam z A (tmlam z A (tmapp (tmvar z) (tmvar z)))) -> False).
Proof.
  intros Hxy Hxz Hyz Halpha.
  inversion Halpha; subst.
  simpl in H5.
  repeat rewrite String.eqb_refl in H5.
  assert (x =? y = false) by admit.
  rewrite H in H5.
  inversion H5; subst.
  simpl in H8.
  assert (y =? fr = false) by admit.
  rewrite H0 in H8.
  repeat rewrite String.eqb_refl in H8.
  inversion H8; subst.
  inversion H7; subst.
  (* Contradiction in H3: fr0 is not fresh over tmapp (tmvar fr0) (tmvar y))*)
Admitted.

Lemma alpha_var_id {x y z}:
  AlphaVar [] x y -> AlphaVar [(z, z)] x y.
Proof.
  intros HalphaVar.
  inversion HalphaVar. subst... (* x = y*)
  case (y =? z) eqn:yz.
  - apply String.eqb_eq in yz. subst.
    apply  alpha_var_cons; reflexivity.
  - apply alpha_var_diff. 
    + apply String.eqb_neq in yz. symmetry. assumption.
    + apply String.eqb_neq in yz. symmetry. assumption.
    + assumption.
Qed.

Require Import Coq.Program.Equality.

(* ******
  Alpha is a contextual equivalence relation *)

Inductive AlphaCtxRefl : list (string * string) -> Set :=
| alpha_refl_nil : AlphaCtxRefl []
| alpha_refl_cons x ren :
    AlphaCtxRefl ren -> 
    AlphaCtxRefl ((x, x) :: ren).

(* Identity alphavar context *)
Lemma alphavar_refl {s ren }:
  AlphaCtxRefl ren -> AlphaVar ren s s.
Proof.
  intros Halphactx.
  induction Halphactx.
  - constructor.
  - destr_eqb_eq x s;
    now constructor.
Qed.

(* Identity alpha context *)
Lemma alpha_refl {s ren}:
  AlphaCtxRefl ren -> Alpha ren s s.
Proof.
  generalize dependent ren.
  induction s; intros ren Hid;
  constructor; auto.
  - now apply alphavar_refl.
  - apply (IHs ((s, s) :: ren)).
    now apply alpha_refl_cons.
Qed.


Inductive AlphaCtxSym : list (string * string) -> list (string * string) -> Set :=
| alpha_sym_nil : AlphaCtxSym [] []
| alpha_sym_cons x y ren ren' :
    AlphaCtxSym ren ren' -> 
    AlphaCtxSym ((x, y) :: ren) ((y, x) :: ren').

Lemma alpha_sym {s t ren ren'}: 
  AlphaCtxSym ren ren' -> Alpha ren s t -> Alpha ren' t s.
Proof with auto. 
  intros Hsym Halpha.
  generalize dependent ren'.
  induction Halpha; 
  intros ren' Hsym;
  constructor...
  - generalize dependent x.
    generalize dependent y.
    induction Hsym.
    + inversion 1.
      apply alpha_var_refl.
    + inversion 1; subst.
      * apply alpha_var_cons...
      * apply alpha_var_diff...
  - apply IHHalpha.
    now apply alpha_sym_cons.
Qed.

Lemma alphavar_sym {s t ren ren'}:
  AlphaCtxSym ren ren' -> AlphaVar ren s t -> AlphaVar ren' t s.
Proof.
  intros.
  assert (Alpha ren (tmvar s) (tmvar t)) by now apply alpha_var.
  eapply alpha_sym in H1; eauto.
  inversion H1; subst; auto.
Qed.


Inductive αCtxTrans : list (string * string) -> list (string * string) -> list (string * string) -> Set :=
| alpha_trans_nil : αCtxTrans [] [] []
| alpha_trans_cons x y z ren ren' ren'' :
    αCtxTrans ren ren' ren'' -> 
    αCtxTrans ((x, y) :: ren) ((y, z) :: ren') ((x, z) :: ren'').


(* Do we also have:
  Alpha ((s, t)::ren) x y -> Alpha (t, u) y z -> Alpha (s, u)::ren x z ?
  
*)
Lemma alpha_trans {s t u ren ren' ren''}: (* Transitive contexts as well *)
  αCtxTrans ren ren' ren'' -> Alpha ren s t -> Alpha ren' t u -> Alpha ren'' s u.
Proof with auto. 
  intros Htrans Halpha1 Halpha2.
  generalize dependent ren'.
  generalize dependent ren''.
  generalize dependent u.
  induction Halpha1; 
  intros u ren'' ren' Htrans Halpha2;
  inversion Halpha2; subst;
  constructor.
  - induction Htrans.
    + inversion H1.
      subst.
      assumption.
      
    + inversion H1; subst.
      inversion a; subst; try contradiction.
      * apply alpha_var_cons.
      * apply alpha_var_diff.
        -- inversion a. subst. contradiction. assumption.
        -- assumption.
        -- apply IHHtrans.
           inversion a.
           ++ contradiction.
           ++ assumption.
           ++ apply alpha_var.
              assumption.
           ++ assumption.
  - apply (IHHalpha1 s3 ((x, y0)::ren'') ((y, y0)::ren')).
    + now apply alpha_trans_cons.
    + now inversion Halpha2.
  - now apply (IHHalpha1_1 s3 ren'' ren').
  - now apply (IHHalpha1_2 t3 ren'' ren').
Qed.

Lemma alpha_var_trans {s t u ren ren' ren''}:
  αCtxTrans ren ren' ren'' -> AlphaVar ren s t -> AlphaVar ren' t u -> AlphaVar ren'' s u.
Proof.
  intros Htrans Halpha1 Halpha2.
  assert (Alpha ren'' (tmvar s) (tmvar u)). {
    eapply alpha_trans; eauto.
    apply alpha_var in Halpha1; eauto.
    apply alpha_var. assumption.
  }
  inversion H.
  assumption.
Qed.

Fixpoint sym_alpha_ctx (ren : list (string * string)) :=
  match ren with
  | nil => nil
  | (x, y) :: ren' => ((y, x) :: (sym_alpha_ctx ren'))
  end.

Lemma sym_alpha_ctx_is_sym ren :
  AlphaCtxSym ren (sym_alpha_ctx ren).
Proof.
  induction ren.
  - simpl.
    constructor.
  - simpl.
    destruct a as [x y].
    apply alpha_sym_cons.
    assumption.
Qed.

Lemma sym_alpha_ctx_left_is_sym ren :
  AlphaCtxSym (sym_alpha_ctx ren) ren.
Proof.
  induction ren.
  - simpl.
    constructor.
  - simpl.
    destruct a as [x y].
    apply alpha_sym_cons.
    assumption.
Qed.
    

Inductive IdCtx : list (string * string) -> Set :=
| id_ctx_nil : IdCtx []
| id_ctx_cons x ren :
    IdCtx ren -> 
    IdCtx ((x, x) :: ren).

Lemma sym_alpha_ctx_preserves_id_ctx ren :
  IdCtx ren -> IdCtx (sym_alpha_ctx ren).
Proof.
Admitted.

Lemma alphavar_unique_right X Y Y' ren :
  AlphaVar ren X Y -> AlphaVar ren X Y' -> Y = Y'.
Proof with subst; auto; try contradiction.
  intros Halpha1 Halpha2.
  induction ren.
  all: inversion Halpha2...
  all: inversion Halpha1...
Qed.

Lemma alphavar_unique_left X X' Y ren :
  AlphaVar ren X Y -> AlphaVar ren X' Y -> X = X'.
Proof with subst; auto; try contradiction.
  intros Halpha1 Halpha2.
  induction ren.
  all: inversion Halpha2...
  all: inversion Halpha1...
Qed.

Lemma alphavar_unique_not_left X X' Y Y' ren :
  X <> X' -> AlphaVar ren X Y -> AlphaVar ren X' Y' -> Y <> Y'.
Proof with subst; auto.
  intros Hneq Halpha1 Halpha2.
  induction ren.
  all: inversion Halpha2... 
  all: inversion Halpha1... 
Qed.

Lemma alphavar_unique_not_right X X' Y Y' ren :
  Y <> Y' -> AlphaVar ren X Y -> AlphaVar ren X' Y' -> X <> X'.
Proof with subst; auto.
  intros Hneq Halpha1 Halpha2.
  induction ren.
  all: inversion Halpha2... 
  all: inversion Halpha1... 
Qed.

(* Predicate that a variable is neither a key nor value in a variable mapping *)
Inductive NotShadowing : string -> list (string * string) -> Set :=
| not_shadow_nil x : NotShadowing x []
| not_shadow_cons z x x' ren :
    z <> x -> 
    z <> x' -> 
    NotShadowing z ren -> 
    NotShadowing z ((x, x') :: ren)
| not_shadow_id z ren :
    NotShadowing z ren -> (* Do we need this? Maybe not, see below*)
    NotShadowing z ((z, z) :: ren).

(* Like the above, but we can now add (z,z) pairs to contexts that already have some
  pairs that "break" shadowing (i.e., they shadow),
  e.g. if we have (x,x);(x, y),
  We can add (x,x) to the front without adding any more "breaking", it behaves the same. *)
Inductive NotBreakShadowing : string -> list (string * string) -> Set :=
| not_break_shadow_nil x : NotBreakShadowing x []
| not_break_shadow_cons z x x' ren :
    z <> x -> 
    z <> x' -> 
    NotBreakShadowing z ren -> 
    NotBreakShadowing z ((x, x') :: ren)
| not_break_shadow_id z ren :
    NotBreakShadowing z ((z, z) :: ren).

Lemma idCtxNotBreakShadowing {x ren}:
  IdCtx ren -> NotBreakShadowing x ren.
Proof.
  intros Hid.
  induction ren.
      * apply not_break_shadow_nil.
      * destruct a as [ax ay].
        assert (ax = ay). { inversion Hid. reflexivity. }
        subst.
        destr_eqb_eq x ay.
        -- apply not_break_shadow_id.
        -- apply not_break_shadow_cons; try assumption.
           inversion Hid. apply IHren. assumption.
Qed.

(* Substitutions that only do renamings. *)
Inductive RenamingSubst : list (string * term) -> Set :=
| rs_nil : RenamingSubst []
| rs_cons x x' sigma :
    RenamingSubst sigma -> 
    RenamingSubst ((x, tmvar x') :: sigma).

(* A ren swap is legal if we swap a pair where their elements are not equal *)
Inductive LegalRenSwap : list (string * string) -> list (string * string) -> Set :=
| lrs_nil : LegalRenSwap [] []
| lrs_cons x y ren1 ren1' :
    LegalRenSwap ren1 ren1' ->
    LegalRenSwap ((x, y)::ren1) (((x, y)::ren1'))
| lrs_start x y v w ren1 ren1' :
    x <> v ->
    y <> w ->
    LegalRenSwap ren1 ren1' -> (* Not important whether x, y, v, w in this, because the two were before them and they still are*)
    LegalRenSwap ((x, y) :: (v, w) :: ren1) ((v, w) :: (x, y) :: ren1').

Lemma legalRenSwap_id {ren}:
  LegalRenSwap ren ren.
Proof.
  induction ren.
  - apply lrs_nil.
  - destruct a as [x y].
    apply lrs_cons.
    assumption.
Qed.

Lemma lrs_trans ren1 ren2 ren3 :
  LegalRenSwap ren1 ren2 -> LegalRenSwap ren2 ren3 -> LegalRenSwap ren1 ren3.
Admitted.

Lemma lrs_sym ren1 ren2 :
  LegalRenSwap ren1 ren2 -> LegalRenSwap ren2 ren1.
Admitted.

Lemma alphavar_weaken {v w ren s t} :
  v <> s -> w <> t -> AlphaVar ((v, w)::ren) s t -> AlphaVar ren s t.
Proof.
  intros Hvs Hwt Halpha.
  inversion Halpha; auto; subst.
  contradiction Hvs. reflexivity.
Qed.

Lemma alphavar_cons_helper { v w w' ren } :
  AlphaVar ((v, w)::ren) v w' -> w = w'.
Proof.
  intros Halpha.
  inversion Halpha; subst.
  - reflexivity.
  - contradiction H2. reflexivity.
Qed.

Lemma alphavar_diff_helper { v z w w' ren } :
  v <> z -> AlphaVar ((v, w)::ren) z w' -> w <> w'.
Proof.
  intros Hvz Halpha.
  inversion Halpha; subst.
  - contradiction Hvz. reflexivity.
  - assumption.
Qed.

Lemma alphavar_swap {s t ren ren'} :
  LegalRenSwap ren ren' ->
  AlphaVar ren s t -> AlphaVar ren' s t.
Proof.
  intros Hswap Halpha.
  generalize dependent ren'.
  dependent induction Halpha; intros ren' Hswap. subst.
  - inversion Hswap.
    apply alpha_var_refl.
  - subst.
    inversion Hswap; subst.
    + apply alpha_var_cons; reflexivity.
    + apply alpha_var_diff.
      * auto.
      * auto.
      * apply alpha_var_cons; reflexivity.
  - dependent induction Hswap. 
    + apply alpha_var_diff; try auto.
    + 
    (* From Halpha, we know that if v = z, then also w0 = w
      so either v=z & w0=w, or v!=z & w0!=w.
    *)
      destruct (v =? z) eqn:vz.
      * assert (v = z).
        {
          apply String.eqb_eq in vz.
          assumption.
        }
        assert (w0 = w).
        {
          subst.
          apply alphavar_cons_helper in Halpha.
          assumption.
        }
        subst.
        apply alpha_var_cons; reflexivity.
      * assert (v <> z). { apply String.eqb_neq in vz. assumption. }

        assert (w0 <> w). {
          apply (alphavar_diff_helper H) in Halpha.
          subst.
          assumption.
        }
        apply alpha_var_diff; try auto.
        apply alpha_var_diff; try auto.
        specialize (IHHalpha ((v, w0)::ren1') (lrs_cons v w0 Hswap)).
        exact (alphavar_weaken H H0 IHHalpha).
Qed.

Lemma alpha_swap {s t ren'} ren :
  LegalRenSwap ren ren' ->
  Alpha ren s t -> Alpha ren' s t.
Proof.
  intros Hswap Halpha.
  generalize dependent ren'.
  induction Halpha; intros ren'; intros lrs.
  - apply alpha_var.
    apply (alphavar_swap lrs a).
  - apply alpha_lam.
    assert (LegalRenSwap ((x, y)::sigma) ((x, y)::ren')) as Hlrs_xy.
    {
      apply lrs_cons.
      assumption.
    }
    specialize (IHHalpha ((x, y) :: ren') Hlrs_xy).
    assumption.
  - apply alpha_app.
    + exact (IHHalpha1 ren' lrs).
    + exact (IHHalpha2 ren' lrs).
Qed.

(* In particular we can now swap identity renamings *)
Lemma alpha_swap_example x y s t :
  Alpha ((x, x)::(y, y)::nil) s t ->
  Alpha ((y, y)::(x, x)::nil) s t.
Proof.
  intros Halpha.
  destruct (x =? y) eqn:xy.
  + apply String.eqb_eq in xy. subst.
    assumption.
  + apply String.eqb_neq in xy.
    apply alpha_swap with (ren := ((x, x)::(y, y)::nil)); [|assumption].
    apply lrs_start; auto.
    apply lrs_nil.
Qed.

(* ******************
         Alpha identity renamings 
   ***************** *)


Import Coq.Program.Equality.

Fixpoint ctx_id_left (ren : list (string * string)) : list (string * string) :=
  match ren with
    | nil => nil
    | (x, y)::ren' => (x, x)::(ctx_id_left ren')  
  end.

Fixpoint ctx_id_right (ren : list (string * string)) : list (string * string) :=
  match ren with
    | nil => nil
    | (x, y)::ren' => (y, y)::(ctx_id_right ren')  
  end.

Lemma ctx_id_left_is_id ren : IdCtx (ctx_id_left ren).
Proof.
  induction ren.
  - simpl. apply id_ctx_nil.
  - destruct a.
    simpl.
    apply id_ctx_cons.
    assumption.
Qed.

Lemma ctx_id_right_is_id ren : IdCtx (ctx_id_right ren).
Proof.
  induction ren.
  - simpl. apply id_ctx_nil.
  - destruct a.
    simpl.
    apply id_ctx_cons.
    assumption.
Qed.

Lemma id_left_trans (ren : list (string * string)) :
  αCtxTrans (ctx_id_left ren) ren ren.
Proof.
  induction ren.
  - simpl. apply alpha_trans_nil.
  - destruct a as [ax ay].
    unfold ctx_id_left. fold ctx_id_left.
    apply alpha_trans_cons.
    assumption.
Qed.

Lemma id_right_trans (ren : list (string * string)) :
  αCtxTrans ren (ctx_id_right ren) ren.
Proof.
  induction ren.
  - simpl. constructor.
  - destruct a as [ax ay].
    unfold ctx_id_right. fold ctx_id_right.
    constructor.
    assumption.
Qed.

Lemma cons_split_helper {x y ren1 ren2} (sigma : list (string * string)) :
  ((x, y):: sigma) = ren1 ++ ren2 -> 
    sum ( {ren1' & ren1 = ((x, y)::ren1')}) (
    (prod (ren1 = nil) (ren2 = ((x, y)::sigma)))).
Proof.
  intros HrenAdd.
  destruct ren1.
  - simpl in HrenAdd.
    right. split.
    + reflexivity.
    + symmetry.
      assumption.
  - simpl in HrenAdd.
    inversion HrenAdd; subst.
    left. exists ren1. reflexivity.
Qed.

Lemma shadow_helper_not_break {z x y ren } :
  NotBreakShadowing z ((x, y)::ren) -> sum 
  (prod (z = x) (z = y)) (prod(z <> x) (z <> y)).
Proof.
  intros Hshadow.
  inversion Hshadow; subst.
  - right. split; assumption.
  - left. split; reflexivity.
Qed.

Lemma alphaVar_then_no_shadow {x y ren} :
  x <> y -> AlphaVar ren x y -> prod (NotBreakShadowing x ren -> False) (NotBreakShadowing y ren -> False).
Proof.
  intros Hxy Halpha.
  split; induction Halpha; intros Hshadow; inversion Hshadow; subst; try contradiction.
  - specialize (IHHalpha Hxy). contradiction.
  - specialize (IHHalpha Hxy H5). contradiction.
Qed.

Require Import Coq.Init.Specif.

(* If we remove a pair from a NotBreakingShadowing environment, it could be an identity pair
  then by not_break_shadow_id we do not necessarily have that 
  ren is a notbreakingshadowing environemnt anymore*)
Lemma weaken_not_break_shadowing {x y z ren} :
  NotBreakShadowing z ((x, y)::ren) -> sum (NotBreakShadowing z ren) (prod (x = z) (y = z)).
Proof.
  intros Hshadow.
  inversion Hshadow; subst.
  - left. assumption.
  - right. split; reflexivity.
Qed.

Lemma alphavar_extend_id_split {x y z} ren :
  AlphaVar ren x y -> 
  forall ren1 ren2, 
    ren = ren1 ++ ren2 -> 
    (* Not break shadowing allows cases like ren2=[(z, z);(z,u)]*)
    NotBreakShadowing z ren2 -> 
    AlphaVar (ren1 ++ ((z, z)::nil) ++ ren2) x y.
Proof.
  intros Halpha.
  dependent induction Halpha; intros ren1 ren2 HrenAdd Hshadow.
  - assert (ren1 = nil).
    {
      destruct ren1.
      - reflexivity.
      - simpl in HrenAdd.
        inversion HrenAdd.
    }
    assert (ren2 = nil). {
      destruct ren2.
      - reflexivity.
      - simpl in HrenAdd.
        subst.
        rewrite app_nil_l in HrenAdd.
        inversion HrenAdd.
    }
    subst.
    (* remove []s*)
    rewrite app_nil_l.
    rewrite app_nil_r.
    destruct (x =? z) eqn:xz.
    + apply String.eqb_eq in xz. subst.
      apply alpha_var_cons; reflexivity.
    + apply String.eqb_neq in xz.
      apply alpha_var_diff; auto.
      apply alpha_var_refl.
  - subst.
    remember (HrenAdd) as HrenAdd'. clear HeqHrenAdd'.
    apply cons_split_helper in HrenAdd.
    destruct HrenAdd as [ [ren1' H ] | [Hren1Empty Hren2Full] ]; subst.
    + apply alpha_var_cons; reflexivity.
    + rewrite app_nil_l.
      apply shadow_helper_not_break in Hshadow.
      destruct Hshadow as [ [Hzz0 Hzw] | [HzNotz0 HzNotw] ]; subst.
      * apply alpha_var_cons; reflexivity.
      * apply alpha_var_diff; try assumption.
        apply alpha_var_cons; reflexivity.
  - remember (HrenAdd) as HrenAdd'. clear HeqHrenAdd'.
    apply cons_split_helper in HrenAdd.
    destruct HrenAdd as [ [ren1' H1] | [ Hren1Empty Hren2Full] ].
    + 
      subst.
      simpl in HrenAdd'.
      apply alpha_var_diff; [assumption|assumption|].
      assert (Hsigmaren1'ren2: sigma = ren1' ++ ren2).
      {
        simpl in HrenAdd'.
        inversion HrenAdd'.
        reflexivity.
      }
      apply (IHHalpha ren1' ren2 Hsigmaren1'ren2 Hshadow).
    + 
      subst.
      rewrite app_nil_l.
      destruct (z =? z0) eqn:Hzx, (z =? w) eqn:Hzw.
      * apply String.eqb_eq in Hzx. subst.
        apply String.eqb_eq in Hzw. subst.
        apply alpha_var_cons; reflexivity.
      * 
        apply String.eqb_eq in Hzx. subst.
        apply String.eqb_neq in Hzw.
        apply (alphaVar_then_no_shadow Hzw) in Halpha.
        destruct Halpha as [Halpha _].
        (* Remove (x, y) from NotShadowing*)
        apply (weaken_not_break_shadowing) in Hshadow.
        destruct Hshadow.
        -- contradiction.
        -- destruct p as [H1 _].
           contradiction.
      * exfalso.
        apply String.eqb_eq in Hzw. subst.
        apply String.eqb_neq in Hzx. apply (not_eq_sym) in Hzx.
        apply (alphaVar_then_no_shadow Hzx) in Halpha.
        destruct Halpha as [_ Halpha].
        apply Halpha.
        apply (weaken_not_break_shadowing) in Hshadow.
        destruct Hshadow.
        -- contradiction.
        -- destruct p as [_ H1].
           contradiction.
      * apply String.eqb_neq in Hzx.
        apply String.eqb_neq in Hzw.
        apply alpha_var_diff; auto.
        apply alpha_var_diff; auto.
Qed.

Lemma alpha_extend_id_split {s t z} ren :
  Alpha ren s t -> 
  forall ren1 ren2, 
    ren = ren1 ++ ren2 -> 
    NotBreakShadowing z ren2 ->
    Alpha (ren1 ++ ((z, z)::nil) ++ ren2) s t.
Proof.
  intros Halpha.
  dependent induction Halpha; intros ren1 ren2 HrenAdd Hshadow.
  - apply alpha_var.
    apply (alphavar_extend_id_split a) with (ren1 := ren1) (ren2 := ren2); eauto.
  - apply alpha_lam.
    assert (HxySum: (x, y) :: sigma = ((x, y)::ren1) ++ ren2).
    {
      rewrite HrenAdd.
      reflexivity.
    }
    apply (IHHalpha ((x, y)::ren1) ren2 HxySum Hshadow).
  - apply alpha_app.
    + apply IHHalpha1; auto.
    + apply IHHalpha2; auto.
Qed.

Lemma alpha_extend_ids_right s t ren idCtx:
  IdCtx idCtx ->
  Alpha ren s t -> Alpha (ren ++ idCtx) s t.
Proof.
  intros Hid Halpha.
  induction Hid.
  - rewrite app_nil_r. assumption.
  - simpl. 
    assert (ren ++ (x, x) :: ren0 = (ren ++ ((x, x)::nil) ++ ren0)).
    {
      rewrite app_assoc. reflexivity.
    }
    rewrite H.
    apply alpha_extend_id_split with (ren1 := ren) (ren2 := ren0) (ren := ren ++ ren0).
    + assumption.
    + reflexivity.
    + now apply @idCtxNotBreakShadowing with (x := x) in Hid. 
Qed.

Lemma alphavar_extend_ids idCtx s t:
  IdCtx idCtx -> AlphaVar nil s t -> AlphaVar idCtx s t.
Proof.
Admitted.

Lemma alpha_extend_ids idCtx s t:
  IdCtx idCtx -> Alpha nil s t -> Alpha idCtx s t.
Proof.
  eapply alpha_extend_ids_right.
Qed.

Lemma alpha_weaken_ids idCtx s t:
  IdCtx idCtx -> Alpha idCtx s t -> Alpha nil s t.
Proof.
Admitted.

Lemma alpha_ids s idCtx :
  IdCtx idCtx -> Alpha idCtx s s.
Proof.
  intros Hid.
  change (idCtx) with (nil ++ idCtx).
  apply alpha_extend_ids_right; auto.
  apply alpha_refl.
  apply alpha_refl_nil.
Qed.



(* **** Stronger! 
      Extend alpha context by a non-shadowing identity substitution, 
      and the result is still alpha equivalent to the original term.

      Alpha [] (tmlam x. s(x)) (tmlam y. s(y))

      Add renaming: (x, x)

      Then:
      Alpha [(x,x)] (tmlam x. s(x)) (tmlam y. s(y))
        by alpha_lam
      Alpha [(x, y), (x, x)] s(x) s(y)
        yes.
*)
Lemma alpha_extend_id' {s t z ren}:
  Alpha ren s t -> NotBreakShadowing z ren -> Alpha ((z, z)::ren ) s t.
Proof.
  intros Halpha.
  intros Hren.
  apply alpha_extend_id_split with (ren := ren) (ren1 := nil); eauto.
Qed. 

(* Since we have Alpha ren s s, we know no ftv in s is in ren! (or it is identity, so we already no that we won't get breaking
  and if we do it is with variables that do not do antying to s
)*)
Lemma alpha_extend_id'' {s z ren}:
  Alpha ren s s -> Alpha ((z, z)::ren ) s s.
Proof.
Admitted.

(* We can extend alpha context by a non-shadowing identity substitution *)
Lemma alpha_extend_id {s z ren}:
  NotBreakShadowing z ren -> Alpha ren s s -> Alpha ((z, z)::ren ) s s.
Proof.
  intros Hren.
  intros Halpha.
  apply alpha_extend_id'; assumption.
Qed.
(*
  We could prove something even stronger:
  Possibly ren already contains some things that break shadowing.
  e.g. ren = (x, x), (x, x'). Then it is perfectly okay to add another (x, x).
*)

(*
Alpha [] (tmlam x A x) (tmlam y A y)
->
Alpha [] (tmlam x A (tmlam x A x)) (tmlam x A (tmlam y A y))

We do not yet use this. Just checking if the alpha machinery is powerful enough
*)
Lemma freshVarAlpha x s t A :
  Alpha [] s t -> Alpha [] (tmlam x A s) (tmlam x A t).
Proof. 
  intros Halpha.
  apply alpha_lam.
  apply alpha_extend_id'.
  - assumption.
  - apply not_break_shadow_nil.
Qed.   

(*
  Suppose x in tv s.
  Then Alpha [(x, x); (x, x')] s s
  => (alpha_cons)
    Alpha [(x, x)] x x

  Otherwise it is not in s, and so the (x, x') is vacuous.
We need the freshness condition since we do not have:
  Alpha [(x, x); (x, x')] x' x'
  *)
Lemma alphaIdShadowsVacuous x x' s :
  ~ (In x' (tv s)) -> Alpha [(x, x); (x, x')] s s.
Proof.
  intros Hfresh.
  induction s.
  -  (* Case: variable *)
    apply alpha_var.
    destr_eqb_eq x s.
    + now apply alpha_var_cons.
    + apply not_in_cons in Hfresh as [Hfresh _].
      now repeat apply alpha_var_diff;
      try apply alpha_var_refl.
  - (* Case: lambda *)
    apply alpha_lam.
    apply not_in_cons in Hfresh as [HfreshS HfreshS0].
    destr_eqb_eq x' x;
    destr_eqb_eq x s.
    all: 
        apply alpha_extend_id;
        [ repeat try constructor; now try assumption
        | now apply IHs ].
  - (* Case: app *)
    apply alpha_app;
    [apply IHs1 | apply IHs2]; 
    now apply not_in_app in Hfresh as [Hfresh1 Hfresh2].
Qed.

(* WHY DO WE HAVE THIS? WHY NOT FTV?*)
Lemma alpha_extend_vacuous {x x' s s' ren}:
  ~ (In x (ftv s)) -> ~ (In x' (tv s')) -> Alpha ren s s' -> Alpha ((x, x')::ren) s s'.
Proof.
Admitted.

Lemma alpha_extend_vacuous_ftv {x x' s s' ren}:
  ~ (In x (ftv s)) -> ~ (In x' (ftv s')) -> Alpha ren s s' -> Alpha ((x, x')::ren) s s'.
Proof.
Admitted.

(* definitions for that? *)
Lemma alpha_extend_vacuous_right {s s' R R'}:
  (forall x, In x (map fst R') -> ~ In x (ftv s)) -> 
  (forall x, In x (map snd R') -> ~ In x (ftv s')) -> Alpha R s s' -> Alpha (R ++ R') s s'.
Proof.
Admitted.

Lemma alpha_extend_vacuous_single {x x' s}:
  ~ (In x (ftv s)) -> ~ (In x' (tv s)) -> Alpha ((x, x')::nil) s s.
Proof.
Admitted.