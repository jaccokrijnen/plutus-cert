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
| alpha_lam B x y A s1 s2 sigma :
    Alpha ((x, y) :: sigma) s1 s2 -> 
    Alpha sigma (@tmlam B x A s1) (@tmlam B y A s2)
| alpha_app B s1 s2 t1 t2 sigma :
    Alpha sigma s1 s2 -> 
    Alpha sigma t1 t2 -> 
    Alpha sigma (@tmapp B s1 t1) (@tmapp B s2 t2)
| alpha_builtin R d :
    Alpha R (tmbuiltin d) (tmbuiltin d).

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

(* **** Examples *)

(* Example of alpha equivalence *)


Lemma alpha_exampl x y y' A :
  x <> y -> y <> y' -> x <> y' -> 
  Alpha [] (@tmlam Lam x A (@tmlam Lam y A (@tmapp App (tmvar x) (tmvar y)))) (@tmlam Lam y A (@tmlam Lam y' A (@tmapp App (tmvar y) (tmvar y')))).
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
  (Alpha [] (@tmlam Lam x A (@tmlam Lam y A (@tmapp App (tmvar x) (tmvar y)))) 
    (@tmlam Lam z A (@tmlam Lam z A (@tmapp App (tmvar z) (tmvar z)))) -> False).
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
  - constructor.
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
  - constructor.
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
Lemma freshVarAlpha B x s t A :
  Alpha [] s t -> Alpha [] (@tmlam B x A s) (@tmlam B x A t).
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
  - constructor.
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

Lemma alpha_vacuous_R {s s' R1 R2}:
  (forall x x', In (x, x') R1 -> prod (~ In x (ftv s)) (~ In x' (ftv s')) ) -> Alpha R2 s s' -> Alpha (R1 ++ R2) s s'.
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