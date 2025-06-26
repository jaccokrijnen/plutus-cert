(** * Strong Normalization of System F *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From Coq Require Import ssrfun.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From PlutusCert Require Import Util.List variables util.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Require Import Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From PlutusCert Require Import STLC util.

(* Helper inductive for alpha equivalent variables *)
Inductive AlphaVar : list (string * string) -> string -> string -> Set :=
| alpha_var_refl x : AlphaVar [] x x
| alpha_var_cons z w R :
    AlphaVar ((z, w) :: R) z w
| alpha_var_diff x y z w R :
    x <> z -> 
    y <> w -> 
    AlphaVar R z w -> 
    AlphaVar ((x, y) :: R) z w.

(* Alpha equivalence with a renaming context *)
Inductive Alpha : list (string * string) -> term -> term -> Set :=
| alpha_var x y R : 
    AlphaVar R x y -> 
    Alpha R (tmvar x) (tmvar y)
| alpha_lam B x y A s1 s2 R :
    Alpha ((x, y) :: R) s1 s2 -> 
    Alpha R (@tmabs B x A s1) (@tmabs B y A s2)
| alpha_app B s1 s2 t1 t2 R :
    Alpha R s1 s2 -> 
    Alpha R t1 t2 -> 
    Alpha R (@tmbin B s1 t1) (@tmbin B s2 t2)
| alpha_builtin R d :
    Alpha R (tmbuiltin d) (tmbuiltin d).

(* ****** Alpha is a contextual equivalence relation *)

Inductive IdCtx : list (string * string) -> Set :=
| id_ctx_nil : IdCtx []
| id_ctx_cons x R :
    IdCtx R -> 
    IdCtx ((x, x) :: R).

(* Identity alphavar context *)
Lemma alphavar_refl {s R }:
  IdCtx R -> AlphaVar R s s.
Proof.
  intros Halphactx.
  induction Halphactx.
  - constructor.
  - destr_eqb_eq x s;
    now constructor.
Qed.

(* Contextual reflexivity *)
Lemma alpha_refl {s R}:
  IdCtx R -> Alpha R s s.
Proof.
  generalize dependent R.
  induction s; intros R Hid;
  constructor; auto.
  - now apply alphavar_refl.
  - apply (IHs ((s, s) :: R)).
    now apply id_ctx_cons.
Qed.

(* Symmetric alpha renaming contexts*)
Inductive AlphaCtxSym : list (string * string) -> list (string * string) -> Set :=
| alpha_sym_nil : AlphaCtxSym [] []
| alpha_sym_cons x y R R1 :
    AlphaCtxSym R R1 -> 
    AlphaCtxSym ((x, y) :: R) ((y, x) :: R1).

(* Contextual symmetry*)
Lemma alpha_sym {s t R R1}: 
  AlphaCtxSym R R1 -> Alpha R s t -> Alpha R1 t s.
Proof with auto. 
  intros Hsym Halpha.
  generalize dependent R1.
  induction Halpha; 
  intros R1 Hsym;
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

(* Var specialization for contextual symmetry*)
Lemma alphavar_sym {s t R R'}:
  AlphaCtxSym R R' -> AlphaVar R s t -> AlphaVar R' t s.
Proof.
  intros.
  assert (Alpha R (tmvar s) (tmvar t)) by now apply alpha_var.
  eapply alpha_sym in H1; eauto.
  inversion H1; subst; auto.
Qed.

(* Transtitive alpha renaming contexts*)
Inductive αCtxTrans : list (string * string) -> list (string * string) -> list (string * string) -> Set :=
| alpha_trans_nil : αCtxTrans [] [] []
| alpha_trans_cons x y z R R1 R2 :
    αCtxTrans R R1 R2 -> 
    αCtxTrans ((x, y) :: R) ((y, z) :: R1) ((x, z) :: R2).

(* Contextual transitivity for variables*)
Lemma alpha_var_trans {s t u R R1 R2}:
  αCtxTrans R R1 R2 -> AlphaVar R s t -> AlphaVar R1 t u -> AlphaVar R2 s u.
Proof.
  intros Htrans Halpha1 Halpha2.
  generalize dependent R1.
  generalize dependent R2.
  generalize dependent u.
  induction Halpha1; 
  intros u R2 R1 Htrans Halpha2.
  + inversion Htrans; subst; auto.
  + inversion Htrans; subst.
    inversion Halpha2; subst; intuition.
    constructor.
  + inversion Htrans; subst.
    inversion Halpha2; subst; intuition.
    constructor; intuition.
Qed.

(* Contextual transitivity *)
Lemma alpha_trans {s t u R R1 R2}: 
  αCtxTrans R R1 R2 -> Alpha R s t -> Alpha R1 t u -> Alpha R2 s u.
Proof with auto. 
  intros Htrans Halpha1 Halpha2.
  generalize dependent R1.
  generalize dependent R2.
  generalize dependent u.
  induction Halpha1; 
  intros u R2 R1 Htrans Halpha2;
  inversion Halpha2; subst;
  constructor.
  - eapply alpha_var_trans; eauto.
  - apply (IHHalpha1 s3 ((x, y0)::R2) ((y, y0)::R1)).
    + now apply alpha_trans_cons.
    + now inversion Halpha2.
  - now apply (IHHalpha1_1 s3 R2 R1).
  - now apply (IHHalpha1_2 t3 R2 R1).
Qed.

(* Generate symmetric version of given renaming context*)
Fixpoint sym_alpha_ctx (R : list (string * string)) :=
  match R with
  | nil => nil
  | (x, y) :: R1 => ((y, x) :: (sym_alpha_ctx R1))
  end.

(* Generated renaming context is symmetric: right*)
Lemma sym_alpha_ctx_is_sym R :
  AlphaCtxSym R (sym_alpha_ctx R).
Proof.
  induction R.
  - simpl.
    constructor.
  - simpl.
    destruct a as [x y].
    apply alpha_sym_cons.
    assumption.
Qed.

(* Generated renaming context is symmetric: left*)
Lemma sym_alpha_ctx_left_is_sym R :
  AlphaCtxSym (sym_alpha_ctx R) R.
Proof.
  induction R.
  - simpl.
    constructor.
  - simpl.
    destruct a as [x y].
    apply alpha_sym_cons.
    assumption.
Qed.

(* Identity renamings have identity left and right lookup behaviour*)
Lemma lookup_id_then_lookup_r (x x' : string) (l : list (string * string)) :
  IdCtx l ->
  lookup x l = Some x ->
  lookup_r x l = Some x.
Proof.
  intros Hid Hl.
  induction Hid.
  - inversion Hl.
  - inversion Hid; subst; auto.
    destr_eqb_eq x x0.
    + apply lookup_r_eq.
    + rewrite lookup_neq in Hl; auto.
      rewrite lookup_r_neq; auto.
Qed.

(* Alpha equivalence is unique: variables, right *)
Lemma alphavar_unique_right X Y Y' R :
  AlphaVar R X Y -> AlphaVar R X Y' -> Y = Y'.
Proof with subst; auto; try contradiction.
  intros Halpha1 Halpha2.
  induction R.
  all: inversion Halpha2...
  all: inversion Halpha1...
Qed.

(* Alpha equivalence is unique: variables, left *)
Lemma alphavar_unique_left X X' Y R :
  AlphaVar R X Y -> AlphaVar R X' Y -> X = X'.
Proof with subst; auto; try contradiction.
  intros Halpha1 Halpha2.
  induction R.
  all: inversion Halpha2...
  all: inversion Halpha1...
Qed.

(* Alpha equivalence is unique: left variable not identical, then right neither *)
Lemma alphavar_unique_not_left X X' Y Y' R :
  X <> X' -> AlphaVar R X Y -> AlphaVar R X' Y' -> Y <> Y'.
Proof with subst; auto.
  intros Hneq Halpha1 Halpha2.
  induction R.
  all: inversion Halpha2... 
  all: inversion Halpha1... 
Qed.

(* Alpha equivalence is unique: right variable not identical, then left neither *)
Lemma alphavar_unique_not_right X X' Y Y' R :
  Y <> Y' -> AlphaVar R X Y -> AlphaVar R X' Y' -> X <> X'.
Proof with subst; auto.
  intros Hneq Halpha1 Halpha2.
  induction R.
  all: inversion Halpha2... 
  all: inversion Halpha1... 
Qed.


(* Inductive that models whether adding an identity renaming to the context shadow (illegally) existing renamings?
  This checks if adding a new renaming "breaks" it, not whether the renaming as a whole is valid.

  - For example: We cannot add (x, x) in front of [(x, y)] -> Then left and right lookup     behaviour is not identical.
  - But: If we already have (x,x);(x, y), We can add (x,x) to the front without adding any more "breaking", it behaves the same. *)
Inductive NotBreakShadowing : string -> list (string * string) -> Set :=
| not_break_shadow_nil x : NotBreakShadowing x []
| not_break_shadow_cons z x x' R :
    z <> x -> 
    z <> x' -> 
    NotBreakShadowing z R -> 
    NotBreakShadowing z ((x, x') :: R)
| not_break_shadow_id z R :
    NotBreakShadowing z ((z, z) :: R).

(* An identity context can always be extended without shadowing *)
Lemma idCtxNotBreakShadowing {x R}:
  IdCtx R -> NotBreakShadowing x R.
Proof.
  intros Hid.
  induction R.
      * apply not_break_shadow_nil.
      * destruct a as [ax ay].
        assert (ax = ay). { inversion Hid. reflexivity. }
        subst.
        destr_eqb_eq x ay.
        -- apply not_break_shadow_id.
        -- apply not_break_shadow_cons; try assumption.
           inversion Hid. apply IHR. assumption.
Qed.

(* A swap of a renaming is legal if we swap a two renamings (x1, y1),(x2,y2) with all distinct elements: then it has the same effect *)
Inductive LegalRenSwap : list (string * string) -> list (string * string) -> Set :=
| lrs_nil : LegalRenSwap [] []
| lrs_cons x y R1 R1' :
    LegalRenSwap R1 R1' ->
    LegalRenSwap ((x, y)::R1) (((x, y)::R1'))
| lrs_start x y v w R1 R1' :
    x <> v ->
    y <> w ->
    LegalRenSwap R1 R1' -> (* Not important whether x, y, v, w in this, because the two were before them and they still are*)
    LegalRenSwap ((x, y) :: (v, w) :: R1) ((v, w) :: (x, y) :: R1').


(* A sequence of legal R swaps*)
Definition LegalRenSwaps := @util.star (list (string * string)) LegalRenSwap.

(**** LegalRenSwap has identity and symmetry *)
Lemma lrs_id {R}:
  LegalRenSwap R R.
Proof.
  induction R.
  - apply lrs_nil.
  - destruct a as [x y].
    apply lrs_cons.
    assumption.
Qed.

Lemma lrs_sym R1 R2 :
  LegalRenSwap R1 R2 -> LegalRenSwap R2 R1.
Proof.
  intros Hlrs.
  induction Hlrs.
  - apply lrs_id.
  - apply lrs_cons. assumption.
  - apply lrs_start; auto.
Qed.


(***** LegalRenSwaps is an equivalence relation *)
Lemma lrss_cons x y R1 R2 :
  LegalRenSwaps R1 R2 ->
  LegalRenSwaps ((x, y)::R1) ((x, y)::R2).
Proof.
  induction 1.
  all: econstructor; eauto.
  constructor; auto.
Qed.

Lemma lrss_intro R1 R2 :
  LegalRenSwap R1 R2 -> 
  LegalRenSwaps R1 R2.
Proof.
  intros.
  econstructor.
  - constructor.
  - auto.
Qed.

Lemma lrss_left R1 R2 ren3 :
  LegalRenSwap R1 R2 -> LegalRenSwaps R2 ren3 ->  LegalRenSwaps R1 ren3.
Proof.
  intros Hlrs Hlrss.
  induction Hlrss.
  - apply lrss_intro. auto.
  - econstructor. eauto. auto.
Qed.

Lemma lrss_sym R1 R2 :
  LegalRenSwaps R1 R2 -> LegalRenSwaps R2 R1.
Proof.
  induction 1.
  - constructor.
  - eapply lrss_left; eauto. apply lrs_sym. auto.
Qed.

Lemma lrss_trans R1 R2 ren3 : 
  LegalRenSwaps R1 R2 -> 
  LegalRenSwaps R2 ren3 -> 
  LegalRenSwaps R1 ren3.
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


(* Removing an unused renaming from the renaming context*)
Lemma alphavar_weaken {v w R s t} :
  v <> s -> w <> t -> AlphaVar ((v, w)::R) s t -> AlphaVar R s t.
Proof.
  intros Hvs Hwt Halpha.
  inversion Halpha; auto; subst.
  contradiction Hvs. reflexivity.
Qed.

(* Helper function for the alphavar cons rule*)
Lemma alphavar_cons_helper { v w w' R } :
  AlphaVar ((v, w)::R) v w' -> w = w'.
Proof.
  intros Halpha.
  inversion Halpha; subst.
  - reflexivity.
  - contradiction H2. reflexivity.
Qed.

(* Helper function for the alphavar diff rule*)
Lemma alphavar_diff_helper { v z w w' R } :
  v <> z -> AlphaVar ((v, w)::R) z w' -> w <> w'.
Proof.
  intros Hvz Halpha.
  inversion Halpha; subst.
  - contradiction Hvz. reflexivity.
  - assumption.
Qed.

(* We can swap a renaming context if we have LegalRenSwap: variable case *)
Lemma alphavar_swap {s t R R1} :
  LegalRenSwap R R1 ->
  AlphaVar R s t -> AlphaVar R1 s t.
Proof.
  intros Hswap Halpha.
  generalize dependent R1.
  dependent induction Halpha; intros R1 Hswap. subst.
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
        specialize (IHHalpha ((v, w0)::R1') (lrs_cons v w0 Hswap)).
        exact (alphavar_weaken H H0 IHHalpha).
Qed.

(* Fundamental property of LegalRenSwap:
   We can swap a renaming context
*)
Lemma alpha_swap {s t R1} R :
  LegalRenSwap R R1 ->
  Alpha R s t -> Alpha R1 s t.
Proof.
  intros Hswap Halpha.
  generalize dependent R1.
  induction Halpha; intros R1; intros lrs.
  - apply alpha_var.
    apply (alphavar_swap lrs a).
  - apply alpha_lam.
    assert (LegalRenSwap ((x, y)::R) ((x, y)::R1)) as Hlrs_xy.
    {
      apply lrs_cons.
      assumption.
    }
    specialize (IHHalpha ((x, y) :: R1) Hlrs_xy).
    assumption.
  - apply alpha_app.
    + exact (IHHalpha1 R1 lrs).
    + exact (IHHalpha2 R1 lrs).
  - constructor.
Qed.

(* We can swap renaming contexts with multiple renaming pairs swapped*)
Lemma alpha_swaps { s t R1} R :
  LegalRenSwaps R R1 ->
  Alpha R s t -> Alpha R1 s t.
Proof.
  intros Hlrss Ha.
  induction Hlrss; auto.
  eapply alpha_swap; eauto.
Qed.

(* ******************
         Alpha identity renamings 
   ***************** *)

(* Create identity renaming based on left element of another context *)
Fixpoint ctx_id_left (R : list (string * string)) : list (string * string) :=
  match R with
    | nil => nil
    | (x, y)::R1 => (x, x)::(ctx_id_left R1)  
  end.

(* Create identity renaming based on right element of another context *)
Fixpoint ctx_id_right (R : list (string * string)) : list (string * string) :=
  match R with
    | nil => nil
    | (x, y)::R1 => (y, y)::(ctx_id_right R1)  
  end.

(* Left identity renaming context is an identity context *)
Lemma ctx_id_left_is_id R : IdCtx (ctx_id_left R).
Proof.
  induction R.
  - simpl. apply id_ctx_nil.
  - destruct a.
    simpl.
    apply id_ctx_cons.
    assumption.
Qed.

(* Right identity renaming context is an identity context *)
Lemma ctx_id_right_is_id R : IdCtx (ctx_id_right R).
Proof.
  induction R.
  - simpl. apply id_ctx_nil.
  - destruct a.
    simpl.
    apply id_ctx_cons.
    assumption.
Qed.

(* Left identity renaming context followed by the context R it was generated from is transitive to that R *)
Lemma id_left_trans (R : list (string * string)) :
  αCtxTrans (ctx_id_left R) R R.
Proof.
  induction R.
  - simpl. apply alpha_trans_nil.
  - destruct a as [ax ay].
    unfold ctx_id_left. fold ctx_id_left.
    apply alpha_trans_cons.
    assumption.
Qed.

(* Analogous for right *)
Lemma id_right_trans (R : list (string * string)) :
  αCtxTrans R (ctx_id_right R) R.
Proof.
  induction R.
  - simpl. constructor.
  - destruct a as [ax ay].
    unfold ctx_id_right. fold ctx_id_right.
    constructor.
    assumption.
Qed.

Lemma NotBreakShadowing__not_break {z x y R } :
  NotBreakShadowing z ((x, y)::R) -> sum 
  (prod (z = x) (z = y)) (prod(z <> x) (z <> y)).
Proof.
  intros Hshadow.
  inversion Hshadow; subst.
  - right. split; assumption.
  - left. split; reflexivity.
Qed.

(* Alpha equivalence of two non-distinct variables means we cannot add those variables as identity renamings: this would shadow the renaming of x to y *)
Lemma alphaVar__NotBreakShadowing {x y R} :
  x <> y -> AlphaVar R x y -> prod (NotBreakShadowing x R -> False) (NotBreakShadowing y R -> False).
Proof.
  intros Hxy Halpha.
  split; induction Halpha; intros Hshadow; inversion Hshadow; subst; try contradiction.
  - specialize (IHHalpha Hxy). contradiction.
  - specialize (IHHalpha Hxy H5). contradiction.
Qed.



(* If we remove a pair from a NotBreakingShadowing environment, it could be an identity pair
  then by not_break_shadow_id we do not necessarily have that 
  R is a notbreakingshadowing environemnt anymore*)
Lemma weaken_not_break_shadowing {x y z R} :
  NotBreakShadowing z ((x, y)::R) -> sum (NotBreakShadowing z R) (prod (x = z) (y = z)).
Proof.
  intros Hshadow.
  inversion Hshadow; subst.
  - left. assumption.
  - right. split; reflexivity.
Qed.

(***** Extending renaming contexts with non-breaking identity renamings ******)

(* Strengthened helper: identity renaming in the middle. For variables*)
Lemma alphavar_extend_id_split {x y z} R :
  AlphaVar R x y -> 
  forall R1 R2, 
    R = R1 ++ R2 -> 
    (* Not break shadowing allows cases like R2=[(z, z);(z,u)]*)
    NotBreakShadowing z R2 -> 
    AlphaVar (R1 ++ ((z, z)::nil) ++ R2) x y.
Proof.
  intros Halpha.
  dependent induction Halpha; intros R1 R2 HrenAdd Hshadow.
  - assert (R1 = nil).
    {
      destruct R1.
      - reflexivity.
      - simpl in HrenAdd.
        inversion HrenAdd.
    }
    assert (R2 = nil). {
      destruct R2.
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
    destruct HrenAdd as [ [R1' H ] | [Hren1Empty Hren2Full] ]; subst.
    + apply alpha_var_cons; reflexivity.
    + rewrite app_nil_l.
      apply NotBreakShadowing__not_break in Hshadow.
      destruct Hshadow as [ [Hzz0 Hzw] | [HzNotz0 HzNotw] ]; subst.
      * apply alpha_var_cons; reflexivity.
      * apply alpha_var_diff; try assumption.
        apply alpha_var_cons; reflexivity.
  - remember (HrenAdd) as HrenAdd'. clear HeqHrenAdd'.
    apply cons_split_helper in HrenAdd.
    destruct HrenAdd as [ [R1' H1] | [ Hren1Empty Hren2Full] ].
    + 
      subst.
      simpl in HrenAdd'.
      apply alpha_var_diff; [assumption|assumption|].
      assert (HRren1'R2: R = R1' ++ R2).
      {
        simpl in HrenAdd'.
        inversion HrenAdd'.
        reflexivity.
      }
      apply (IHHalpha R1' R2 HRren1'R2 Hshadow).
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
        apply (alphaVar__NotBreakShadowing Hzw) in Halpha.
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
        apply (alphaVar__NotBreakShadowing Hzx) in Halpha.
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


(* Strengthened helper: identity renaming in the middle. *)
Lemma alpha_extend_id_split {s t z} R :
  Alpha R s t -> 
  forall R1 R2, 
    R = R1 ++ R2 -> 
    NotBreakShadowing z R2 ->
    Alpha (R1 ++ ((z, z)::nil) ++ R2) s t.
Proof.
  intros Halpha.
  dependent induction Halpha; intros R1 R2 HrenAdd Hshadow.
  - apply alpha_var.
    apply (alphavar_extend_id_split a) with (R1 := R1) (R2 := R2); eauto.
  - apply alpha_lam.
    assert (HxySum: (x, y) :: R = ((x, y)::R1) ++ R2).
    {
      rewrite HrenAdd.
      reflexivity.
    }
    apply (IHHalpha ((x, y)::R1) R2 HxySum Hshadow).
  - apply alpha_app.
    + apply IHHalpha1; auto.
    + apply IHHalpha2; auto.
  - constructor.
Qed.

(* Identity renamings can always be added on the right (they cannot shadow anything)*)
Lemma alpha_extend_ids_right s t R idCtx:
  IdCtx idCtx ->
  Alpha R s t -> Alpha (R ++ idCtx) s t.
Proof.
  intros Hid Halpha.
  induction Hid.
  - rewrite app_nil_r. assumption.
  - simpl. 
    assert (R ++ (x, x) :: R0 = (R ++ ((x, x)::nil) ++ R0)).
    {
      rewrite app_assoc. reflexivity.
    }
    rewrite H.
    apply alpha_extend_id_split with (R1 := R) (R2 := R0) (R := R ++ R0).
    + assumption.
    + reflexivity.
    + now apply @idCtxNotBreakShadowing with (x := x) in Hid. 
Qed.

(* Specialization of the above for variables *)
Lemma alphavar_extend_ids_right {s t R idCtx}:
  IdCtx idCtx -> AlphaVar R s t -> AlphaVar (R ++ idCtx) s t.
Proof.
  intros Hid Ha.
  assert (Alpha (R ++ idCtx) (tmvar s) (tmvar t)).
  {
    apply alpha_extend_ids_right; auto.
    constructor. auto.
  }
  inversion H; auto.
Qed.

(* Specialization of identity renaming extension for empty contexts: variable case*)
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

(* Specialization of identity renaming extension for empty contexts *)
Lemma alpha_extend_ids idCtx s t:
  IdCtx idCtx -> Alpha nil s t -> Alpha idCtx s t.
Proof.
  eapply alpha_extend_ids_right.
Qed.

(* Alpha equivalence models consistent left and right lookup*)
Lemma alphavar_models_lookup R s s' :
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

(* Specialization *)
Lemma av_lookup_implies_right R x y :
  AlphaVar R x y -> (lookup x R = Some y -> lookup_r y R = Some x).
Proof.
  intros.
  apply alphavar_models_lookup in H.
  destruct H as [Hyes | Hno].
  - intuition.
  - destruct Hno as [[Hno _] _ ].
    rewrite Hno in H0.
    inversion H0.
Qed.

(* Identity renaming contexts imply identity lookup *)
Lemma lookup_idctx_refl R s t:
  IdCtx R -> lookup s R = Some t -> s = t.
Proof.
  intros Hid Hl.
  induction R; [inversion Hl|].
  - destruct a as [a1 a2].
    inversion Hid; subst.
    inversion Hl.
    destr_eqb_eq a2 s.
    + inversion H1; subst.
      reflexivity.
    + apply IHR; auto.
Qed.

(* Lookup implies alpha equivalence for identity renamings *)
Lemma lookup_some_IdCtx_then_alphavar R s s' :
  IdCtx R -> lookup s R = Some s' -> AlphaVar R s s'.
Proof.
  intros Hid Hl.
  induction R.
  - inversion Hl.
  - destruct a as [a1 a2].
    inversion Hid; subst.
    inversion Hl.
    destr_eqb_eq a2 s.
    + inversion H1; subst.
      constructor.
    + constructor; auto.
      apply lookup_idctx_refl in H1; subst; auto.
Qed.

(* Bothsided lookup models alpha equivalence: Some *)
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
      inversion H.
      constructor.
    + assert (s1 <> s').
      {
        intros Hcontra.
        subst.
        simpl in H0.
        rewrite String.eqb_refl in H0.
        inversion H0.
        contradiction.
      }
      constructor; eauto.
      eapply IHR.
      * apply lookup_cons_helper in H; eauto.
      * apply lookup_r_cons_helper in H0; auto.
Qed.

(* Bothsided lookup models alpha equivalence: None *)
Lemma lookup_none_then_alpharefl R s :
  lookup s R = None -> lookup_r s R = None -> AlphaVar R s s.
Proof.
  intros.
  induction R.
  - simpl. constructor.
  - destruct a.
    constructor.
    + intros Hcontra. subst. simpl in H. rewrite String.eqb_refl in H. inversion H.
    + intros Hcontra. subst. simpl in H0. rewrite String.eqb_refl in H0. inversion H0.
    + eapply IHR; eauto.
      * eapply lookup_cons_None_helper. eauto.
      * eapply lookup_r_cons_None_helper. eauto.
Qed.

(* If s in an identity map on the left, then bothsided lookup finds it as an identity*)
Lemma lookup_id_exists_then_refl R s:
  IdCtx R -> In s (map fst R) ->
  ((lookup s R = Some s) * (lookup_r s R = Some s))%type.
Proof.
  intros Hid HIn.
  induction Hid.
  - inversion HIn.
  - destr_eqb_eq x s.
    + simpl.
      rewrite String.eqb_refl.
      auto.
    + simpl.
      apply String.eqb_neq in H.
      rewrite H.
      apply IHHid.
      inversion HIn; subst; auto.
      simpl in H.
      apply String.eqb_neq in H.
      contradiction.
Qed.

(* If s not in an identity map on the left, then neither on the right *)
Lemma lookup_id_nex_then_not R s:
  IdCtx R -> ~ In s (map fst R) ->
  ((lookup s R = None) * (lookup_r s R = None))%type.
Proof.
  intros Hid HIn.
  induction Hid.
  - simpl. auto.
  - rewrite map_cons in HIn.
    simpl in HIn.
    apply de_morgan2 in HIn as [HIn1 HIn2].
    simpl.
    apply String.eqb_neq in HIn1.
    rewrite HIn1.
    apply IHHid; auto.
Qed.

(* Removing an identity renaming is allowed if it is only followed by other identity renamings: variable case *)
Lemma alphavar_weaken_id R idCtx1 s t x :
  IdCtx ((x, x)::idCtx1) -> AlphaVar (R ++ (x, x)::idCtx1) s t -> AlphaVar (R ++ idCtx1) s t.
Proof.
  intros Hid Ha.
  apply alphavar_models_lookup in Ha.
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


(* Removing an identity renaming is allowed if it is only followed by other identity renamings.

Technically difficult lemma, because when going under binder, we lose the IdCtx "invariant"*)
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

(* Removing identity renamings is allowed *)
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

(* Extending with identity is allowed if it does not do a breaking shadowing *)
Lemma alpha_extend_id {s t z R}:
  Alpha R s t -> NotBreakShadowing z R -> Alpha ((z, z)::R ) s t.
Proof.
  intros Halpha.
  intros Hren.
  apply alpha_extend_id_split with (R := R) (R1 := nil); eauto.
Qed. 

(* Identity substitution from lambda abstraction preserves α-equivalence*)
Lemma freshVarAlpha B x s t A :
  Alpha [] s t -> Alpha [] (@tmabs B x A s) (@tmabs B x A t).
Proof. 
  intros Halpha.
  apply alpha_lam.
  apply alpha_extend_id.
  - assumption.
  - apply not_break_shadow_nil.
Qed.   

(* Names that are not free or bound can be added: they are vacuous renamings *)
Lemma alpha_extend_vacuous {x x' s s' R}:
  ~ (In x (tv s)) -> ~ (In x' (tv s')) -> Alpha R s s' -> Alpha ((x, x')::R) s s'.
Proof.
  intros Hftv_s Hftv_s' Ha_s.
  induction Ha_s.
  - repeat constructor; auto.
    + simpl in Hftv_s. auto.
    + simpl in Hftv_s'. auto.
  - constructor; auto.
    apply alpha_swap with (R := ((x, x')::(x0, y)::R)).
    + constructor; auto.
      * simpl in Hftv_s. auto.
      * simpl in Hftv_s'. auto.
      * apply lrs_id.
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

(* If a name x does not occur in R, then R does not rename x *)
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
  If x' is not in s, then we may shadow the renaming since it is vacuous
  *)
Lemma alpha_id_shadows_vacuous x x' s :
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
        [now apply IHs | repeat try constructor; now try assumption
         ].
  - (* Case: app *)
    apply alpha_app;
    [apply IHs1 | apply IHs2]; 
    now apply not_in_app in Hfresh as [Hfresh1 Hfresh2].
  - constructor.
Qed.

(* Prepending vacuous renamings *)
Lemma alphavar_vacuous_prepend R1 R2 s s' :
  AlphaVar R2 s s' -> lookup s R1 = None -> lookup_r s' R1 = None -> AlphaVar (R1 ++ R2) s s'.
Proof.
  intros.
  induction R1.
  - simpl. auto.
  - destruct a.
    simpl.
    constructor.
    + intros Hcontra.
      subst.
      simpl in H0.
      rewrite String.eqb_refl in H0.
      inversion H0.
    + intros Hcontra.
      subst.
      simpl in H1.
      rewrite String.eqb_refl in H1.
      inversion H1.
    + eapply IHR1; eauto.
      * simpl in H0. destruct_match. auto.
      * simpl in H1. destruct_match. auto.
Qed.


(* Threefold transitivity helper*)
Lemma alpha_trans3 {R s s' s'' s'''}:
  Alpha [] s s' -> Alpha R s' s'' -> Alpha [] s'' s''' -> Alpha R s s'''.
Proof.
  intros.
  eapply @alpha_trans with (R := ctx_id_left R) (R1 := R).
  - { apply id_left_trans. } 
  - apply alpha_extend_ids. apply ctx_id_left_is_id. eauto.
  - eapply @alpha_trans with (R := R) (R1 := ctx_id_right R).
    + apply id_right_trans.
    + eauto.
    + apply alpha_extend_ids. apply ctx_id_right_is_id. eauto.
Qed.