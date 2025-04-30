(** * Strong Normalization of System F *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List AutosubstSsr freshness util.
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

Lemma alpha_var_trans {s t u ren ren' ren''}:
  αCtxTrans ren ren' ren'' -> AlphaVar ren s t -> AlphaVar ren' t u -> AlphaVar ren'' s u.
Proof.
  intros Htrans Halpha1 Halpha2.
  generalize dependent ren'.
  generalize dependent ren''.
  generalize dependent u.
  induction Halpha1; 
  intros u ren'' ren' Htrans Halpha2.
  + inversion Htrans; subst; auto.
  + inversion Htrans; subst.
    inversion Halpha2; subst; intuition.
    constructor.
  + inversion Htrans; subst.
    inversion Halpha2; subst; intuition.
    constructor; intuition.
Qed.

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
  - eapply alpha_var_trans; eauto.
  - apply (IHHalpha1 s3 ((x, y0)::ren'') ((y, y0)::ren')).
    + now apply alpha_trans_cons.
    + now inversion Halpha2.
  - now apply (IHHalpha1_1 s3 ren'' ren').
  - now apply (IHHalpha1_2 t3 ren'' ren').
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
    
(* TODO: This is exactly alphaCtxRefl*)
Inductive IdCtx : list (string * string) -> Set :=
| id_ctx_nil : IdCtx []
| id_ctx_cons x ren :
    IdCtx ren -> 
    IdCtx ((x, x) :: ren).

Lemma lookup_id_then_lookup_r (x x' : string) (l : list (string * string)) :
  IdCtx l ->
  lookup x l = Some x ->
  lookup_r x l = Some x.
Admitted.

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

Definition LegalRenSwaps := @util.star (list (string * string)) LegalRenSwap.


(*
  LRS [a, b, c] [b, a, c]

            LRS [b, a, c] [b, c, a]
? LRS [a, b, c]           [b, c, a] ?

No......
*)

Lemma legalRenSwap_id {ren}:
  LegalRenSwap ren ren.
Proof.
  induction ren.
  - apply lrs_nil.
  - destruct a as [x y].
    apply lrs_cons.
    assumption.
Qed.

Lemma lrs_sym ren1 ren2 :
  LegalRenSwap ren1 ren2 -> LegalRenSwap ren2 ren1.
Proof.
  intros Hlrs.
  induction Hlrs.
  - apply legalRenSwap_id.
  - apply lrs_cons. assumption.
  - apply lrs_start; auto.
Qed.


Lemma lrss_cons x y ren1 ren2 :
  LegalRenSwaps ren1 ren2 ->
  LegalRenSwaps ((x, y)::ren1) ((x, y)::ren2).
Proof.
  induction 1.
  all: econstructor; eauto.
  constructor; auto.
Qed.

Lemma lrss_intro ren1 ren2 :
  LegalRenSwap ren1 ren2 -> 
  LegalRenSwaps ren1 ren2.
Proof.
  intros.
  econstructor.
  - constructor.
  - auto.
Qed.

Lemma lrss_left ren1 ren2 ren3 :
  LegalRenSwap ren1 ren2 -> LegalRenSwaps ren2 ren3 ->  LegalRenSwaps ren1 ren3.
Proof.
  intros Hlrs Hlrss.
  induction Hlrss.
  - apply lrss_intro. auto.
  - econstructor. eauto. auto.
Qed.

Lemma lrss_sym ren1 ren2 :
  LegalRenSwaps ren1 ren2 -> LegalRenSwaps ren2 ren1.
Proof.
  intros.
  induction X.
  - constructor.
  - eapply lrss_left; eauto. apply lrs_sym. auto.
Qed.

Lemma lrss_trans ren1 ren2 ren3 : 
  LegalRenSwaps ren1 ren2 -> 
  LegalRenSwaps ren2 ren3 -> 
  LegalRenSwaps ren1 ren3.
Proof.
  intros Hlrs12 Hlrs23.
  generalize dependent ren3.
  induction Hlrs12; intros.
  - auto.
  - eapply IHHlrs12.
    apply lrss_sym in Hlrs23.
    apply lrss_sym.
    apply lrs_sym in e.
    eapply starSE; eauto.
Qed.


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

Lemma alpha_swaps { s t ren'} ren :
  LegalRenSwaps ren ren' ->
  Alpha ren s t -> Alpha ren' s t.
Proof.
  intros Hlrss Ha.
  induction Hlrss; auto.
  eapply alpha_swap; eauto.
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

Lemma alphavar_extend_ids_right {s t ren idCtx}:
  IdCtx idCtx -> AlphaVar ren s t -> AlphaVar (ren ++ idCtx) s t.
Proof.
  intros Hid Ha.
  assert (Alpha (ren ++ idCtx) (tmvar s) (tmvar t)).
  {
    apply alpha_extend_ids_right; auto.
    constructor. auto.
  }
  inversion H; auto.
Qed.

Lemma alphavar_extend_ids idCtx s t:
  IdCtx idCtx -> AlphaVar nil s t -> AlphaVar idCtx s t.
Proof.
  intros Hid Hav.
  inversion Hav; subst.
  induction Hid.
  - auto.
  - destr_eqb_eq x t.
    + constructor.
    + constructor; auto.
Qed.

Lemma alpha_extend_ids idCtx s t:
  IdCtx idCtx -> Alpha nil s t -> Alpha idCtx s t.
Proof.
  eapply alpha_extend_ids_right.
Qed.

Lemma alphavar_lookup_helper R s s' :
  AlphaVar R s s' -> (((lookup s R = Some s') * (lookup_r s' R = Some s)) + ((lookup s R = None) * (lookup_r s' R = None) * (s = s')))%type.
Proof.
  intros.
  induction H.
  - right. intuition.
  - left. intuition.
    simpl. rewrite String.eqb_refl. auto.
    simpl. rewrite String.eqb_refl. auto.
  - destruct IHAlphaVar as [[IH1 IH2] | [IH1 IH2]].
    + left. split.
      * simpl. rewrite <- String.eqb_neq in n. rewrite n. auto.
      * simpl. rewrite <- String.eqb_neq in n0. rewrite n0. auto.
    + right. split; [split|].
      * simpl. rewrite <- String.eqb_neq in n. rewrite n. destruct IH1 as [IH1 _]. auto.
      * simpl. rewrite <- String.eqb_neq in n0. rewrite n0. destruct IH1 as [_ IH1']. auto.
      * auto.
Qed.

Lemma lookup_some_IdCtx_then_alphavar R s s' :
  IdCtx R -> lookup s R = Some s' -> AlphaVar R s s'.
Admitted.

Lemma lookup_some_then_alphavar R s s' :
  lookup s R = Some s' -> lookup_r s' R = Some s -> AlphaVar R s s'.
Proof.
  intros.
  induction R.
  - inversion H.
  - destruct a.
    destr_eqb_eq s0 s.
    + simpl in H.
      rewrite String.eqb_refl in H.
      inv H.
      constructor.
    + assert (s1 <> s').
      {
        intros Hcontra.
        subst.
        simpl in H0.
        rewrite String.eqb_refl in H0.
        inv H0.
        contradiction.
      }
      constructor; eauto.
      eapply IHR.
      * apply lookup_cons_helper in H; eauto.
      * apply lookup_r_cons_helper in H0; auto.
Qed.

Lemma lookup_cons_None_helper (R : list (string * string)) s x y :
  lookup s ((x, y)::R) = None -> lookup s R = None.
Proof.
  intros.
  simpl in H.
  destruct_match.
  auto.
Qed.

Lemma lookup_r_cons_None_helper (R : list (string * string)) s' x y :
  lookup_r s' ((x, y)::R) = None -> lookup_r s' R = None.
Proof.
  intros.
  simpl in H.
  destruct_match.
  auto.
Qed.

Lemma lookup_none_then_alpharefl R s :
  lookup s R = None -> lookup_r s R = None -> AlphaVar R s s.
Proof.
  intros.
  induction R.
  - simpl. constructor.
  - destruct a.
    constructor.
    + intros Hcontra. subst. simpl in H. rewrite String.eqb_refl in H. inv H.
    + intros Hcontra. subst. simpl in H0. rewrite String.eqb_refl in H0. inv H0.
    + eapply IHR; eauto.
      * eapply lookup_cons_None_helper. eauto.
      * eapply lookup_r_cons_None_helper. eauto.
Qed.

Lemma lookup_idctx_refl R s t:
  IdCtx R -> lookup s R = Some t -> s = t.
Proof.
Admitted.

Lemma lookup_id_exists_then_refl R s:
  IdCtx R -> In s (map fst R) ->
  ((lookup s R = Some s) * (lookup_r s R = Some s))%type.
Admitted.

Lemma lookup_id_nex_then_not R s:
  IdCtx R -> ~ In s (map fst R) ->
  ((lookup s R = None) * (lookup_r s R = None))%type.
Admitted.

Lemma lookup_none_smaller (R1 R2: list (string * string)) s :
  (forall x, In x (map fst R1) -> In x (map fst R2)) -> lookup s R2 = None -> lookup s R1 = None.
Admitted.

Lemma lookupr_none_smaller (R1 R2: list (string * string)) s :
  (forall x, In x (map snd R1) -> In x (map snd R2)) -> lookup_r s R2 = None -> lookup_r s R1 = None.
Admitted.

Lemma alphavar_weaken_id R idCtx1 s t x :
  IdCtx ((x, x)::idCtx1) -> AlphaVar (R ++ (x, x)::idCtx1) s t -> AlphaVar (R ++ idCtx1) s t.
Proof.
  intros Hid Ha.
  apply alphavar_lookup_helper in Ha.
  destruct Ha as [[Hl_some H_lr_some] | [[Hl_none Hlr_none] Heq]].
  - destruct (lookup_split_app_helper _ _ _ _ Hl_some H_lr_some) as [[Hl_R1_some Hlr_R1_some] | [[[Hl_R1_none Hlr_R1_none] Hl_R2_some] Hlr_R2_some]].
    + apply lookup_some_then_alphavar.
      -- apply lookup_some_extend_helper; auto.
      -- apply lookup_some_extend_helper; auto.
    + assert (t = s).
      {
        apply (lookup_idctx_refl Hid) in Hl_R2_some.
        auto.
      }
      subst.
      remember Hl_R2_some as Hl_R2_some'; clear HeqHl_R2_some'.
      simpl in Hl_R2_some'.
      
      destruct (in_dec string_dec s (map fst idCtx1)).
      * inversion Hid; subst.
        destruct (lookup_id_exists_then_refl H0 i) as [Hl_refl Hlr_refl].
        destruct (@lookup_none_extend_helper _ (idCtx1) _ Hl_R1_none Hlr_R1_none) as [Hl_ex Hlr_ex].
        apply lookup_some_then_alphavar; auto.
        -- rewrite Hl_ex. auto.
        -- rewrite Hlr_ex. auto.
      * inversion Hid; subst.
        destruct (lookup_id_nex_then_not H0 n) as [Hl_refl Hlr_refl].
        (* We know that s is not in the idCtx1, so we can use the lookup_none lemma *)
        destruct (@lookup_none_extend_helper _ (idCtx1) _ Hl_R1_none Hlr_R1_none) as [Hl_ex Hlr_ex].
        apply lookup_none_then_alpharefl.
        -- rewrite Hl_ex. auto.
        -- rewrite Hlr_ex. auto.
  - subst.
    apply lookup_none_then_alpharefl.
    -- apply lookup_none_smaller with (R1 := R ++ idCtx1) in Hl_none; auto.
       intros.
       rewrite map_app in H.
       apply in_app_iff in H.
       destruct H as [H_inR | H_inidCtx1].
       ++ apply in_map_iff in H_inR.
          destruct H_inR as [x' [H_eq H_inR]].
          destruct x'.
          simpl in H_eq; subst.
          apply in_map_iff.
          exists ((x0, s0)).
          split.
          ** auto.
          ** apply in_app_iff.
             left. auto.
       ++ apply in_map_iff in H_inidCtx1.
          destruct H_inidCtx1 as [x' [H_eq H_inidCtx1]].
          destruct x'.
          simpl in H_eq; subst.
          apply in_map_iff.
          exists ((x0, s0)).
          split.
          ** auto.
          ** apply in_app_iff.
             right. auto.
             apply in_cons. auto.
    -- apply lookupr_none_smaller with (R1 := R ++ idCtx1) in Hlr_none.
        ++ auto.
        ++ intros.
            rewrite map_app in H.
            apply in_app_iff in H.
            destruct H as [H_inR | H_inidCtx1].
            ** apply in_map_iff in H_inR.
              destruct H_inR as [x' [H_eq H_inR]].
              destruct x'.
              simpl in H_eq; subst.
              apply in_map_iff.
              exists (s, x0).
              split.
              --- auto.
              --- apply in_app_iff.
                  left. auto.
            ** apply in_map_iff in H_inidCtx1.
              destruct H_inidCtx1 as [x' [H_eq H_inidCtx1]].
              destruct x'.
              simpl in H_eq; subst.
              apply in_map_iff.
              exists (s, x0).
              split.
              --- auto.
              --- apply in_app_iff.
                  right. auto.
                  apply in_cons. auto.
Qed.


(* Difficult lemma, because when going under binder, we lose the IdCtx "invariant"*)
Lemma alpha_weaken_id R idCtx1 s t x y :
  IdCtx ((x, y)::idCtx1) -> Alpha (R ++ (x, y)::idCtx1) s t -> Alpha (R ++ idCtx1) s t.
Proof.
  intros.
  assert (x = y). 
  {
    inversion H; subst. reflexivity.
  }
  subst.
  dependent induction H0.
  - constructor.
    eapply alphavar_weaken_id; eauto.
  - constructor.
    change (((x, y0) :: (R ++ idCtx1))) with (((x, y0)::R) ++ idCtx1).
    eapply IHAlpha; eauto.
    + change ((x, y0) :: R ++ (y, y) :: idCtx1 ) with (((x, y0) :: R) ++ (y, y) :: idCtx1).
      auto.
  - constructor.
    + eapply IHAlpha1; eauto.
    + eapply IHAlpha2; eauto.
  - constructor.
Qed.

Lemma alpha_weaken_ids idCtx s t:
  IdCtx idCtx -> Alpha idCtx s t -> Alpha nil s t.
Proof.
  intros Hid Hav.
  induction idCtx.
  - auto.
  - eapply IHidCtx.
    + inversion Hid; auto.
    + destruct a as [x y].
      assert (idCtx = [] ++ idCtx).
      {
        rewrite app_nil_l.
        auto.
      }
      rewrite H.
      eapply alpha_weaken_id; eauto.
Qed.

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
Lemma 
hadowsVacuous x x' s :
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

Lemma alpha_extend_vacuous {x x' s s' R}:
  ~ (In x (tv s)) -> ~ (In x' (tv s')) -> Alpha R s s' -> Alpha ((x, x')::R) s s'.
Proof.
  intros Hftv_s Hftv_s' Ha_s.
  induction Ha_s.
  - repeat constructor; auto.
    + simpl in Hftv_s. auto.
    + simpl in Hftv_s'. auto.
  - constructor; auto.
    apply alpha_swap with (ren := ((x, x')::(x0, y)::sigma)).
    + constructor; auto.
      * simpl in Hftv_s. auto.
      * simpl in Hftv_s'. auto.
      * apply legalRenSwap_id.
    + eapply IHHa_s.
      * eapply not_tv_dc_lam; eauto.
      * eapply not_tv_dc_lam; eauto.
  - constructor.
    + apply IHHa_s1; auto;
      eapply not_tv_dc_appl; eauto.
    + apply IHHa_s2; auto;
      eapply not_tv_dc_appr; eauto.
  - constructor.
Qed.


Lemma alphavar_refl_weaken_vacuouss {x R} :
  ~ In x (map fst R) -> ~ In x (map snd R) -> AlphaVar R x x.
Proof.
  intros H_Rl H_Rr.
  induction R.
  - constructor.
  - destruct a as [a1 a2].
    constructor.
    + simpl in H_Rl.
      apply de_morgan2 in H_Rl as [Hneq _]. auto.
    + simpl in H_Rr.
      apply de_morgan2 in H_Rr as [Hneq _]. auto.
    + eapply IHR.
      * simpl in H_Rl. apply de_morgan2 in H_Rl as [_ H_Rl]. auto.
      * simpl in H_Rr. apply de_morgan2 in H_Rr as [_ H_Rr]. auto.
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
