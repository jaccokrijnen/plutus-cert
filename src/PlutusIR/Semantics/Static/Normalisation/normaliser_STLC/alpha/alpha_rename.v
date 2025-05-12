Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From PlutusCert Require Import STLC_named alpha.alpha Util.List freshness util.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* *************
    Important lemma that shows the relation between alpha contexts and renamings
*)

(* We use bound and free because it is easier to reason about.
 e.g. x not free in any subterm of \x. y
 But it is bound in there.
  while in \x.x it is free in the subterm.
If we just take bound terms always as well, I think it is easier to reason.

Also, we need a freshness condition since renaming is not capture-avoiding.

Correspondence between alpha contexts and renamings on syntactically equal terms.
 *)
Lemma alphaRename x x' s :
  (* x' can be equal to x., but then x=x' not in s, so the renaming doesnt do anything. 
    Cannot easily be restricted to ftv: say s = λ x' . x. Then x' not free in s, but rename x x' s, will cause capture
  *)
  ~ (In x' (tv s)) -> Alpha [(x, x')] s (rename x x' s).
Proof.
  intros Hfresh.
  induction s.
  - unfold rename.
    unfold mren.
    unfold lookup.
    destruct (x =? s) eqn:xs.
    + apply String.eqb_eq in xs.
      subst.
      apply alpha_var.
      apply alpha_var_cons; reflexivity.
    + apply alpha_var.
      apply alpha_var_diff.
      * apply String.eqb_neq in xs.
        assumption.
      * apply not_in_cons in Hfresh.
        destruct Hfresh as [Hfresh _].
        assumption.
      * apply alpha_var_refl.
  - destr_eqb_eq s x.
    + 
    
      assert (HignoreRename: forall B, rename x x' (@tmlam B x k s0) = @tmlam B x k s0).
      {
        unfold rename.
        unfold mren.
        fold mren.
        subst.
        simpl.
        rewrite String.eqb_refl.
        rewrite mren_id.
        reflexivity.
      }
      rewrite HignoreRename.
      apply alpha_lam.
      apply alphaIdShadowsVacuous.
      unfold tv in Hfresh; fold tv in Hfresh.
      apply not_in_cons in Hfresh.
      destruct Hfresh as [_ Hfresh].
      assumption.
    + assert (H1: forall B, rename x x' (@tmlam B s k s0) = @tmlam B s k (rename x x' s0)).
      {
        unfold rename.
        unfold mren.
        fold mren.
        simpl.
        rewrite <- String.eqb_neq in H.
        rewrite String.eqb_sym in H.
        rewrite H.
        auto.        
      }
      rewrite H1.
      apply alpha_lam.
      assert (s <> x').
      {
        apply not_in_cons in Hfresh.
        destruct Hfresh as [Hfresh _].
        symmetry.
        assumption.
      }
      
      apply alpha_extend_id'.
      * apply IHs.
        (* We know tv (tmlam s t s0) = s :: tv s0*)
        (* Hence we make a superset argument: *)
        unfold tv in Hfresh; fold tv in Hfresh.
        (* if x' notin x :: s, then also x' not in x*)
        apply not_in_cons in Hfresh.
        destruct Hfresh.
        assumption.
      * apply not_break_shadow_cons; try assumption.
        apply not_break_shadow_nil.
  - unfold rename.
    unfold mren.
    apply alpha_app; fold mren.
    + apply IHs1.
      unfold tv in Hfresh; fold tv in Hfresh.
      apply not_in_app in Hfresh.
      destruct Hfresh as [Hfresh _].
      assumption.
    + apply IHs2.
      unfold tv in Hfresh; fold tv in Hfresh.
      apply not_in_app in Hfresh.
      destruct Hfresh as [_ Hfresh].
      assumption.
  - unfold rename.
    unfold mren.
    constructor.
Qed.  


(*
 Stronger result where s and s' not syntactically equal
  New idea! Finally work with high-level ideas instead of induction on terms!
*)
Lemma alphaRenameStronger x x' s s' ren :
  ~ (In x' (tv s')) -> 
  NotBreakShadowing x ren ->
  Alpha ren s s' -> Alpha ((x, x')::ren) s (rename x x' s').
Proof.
  intros HnotIns' Hshadow Halpha.
  eapply @alpha_trans with (ren := (x, x)::ren) (ren' := (x, x')::nil ++ ctx_id_right ren).
  - apply alpha_trans_cons.
    apply id_right_trans.
  - apply alpha_extend_id'; eauto.
  - apply alpha_extend_ids_right with (ren := (x, x')::nil).
    + apply ctx_id_right_is_id.
    + now apply alphaRename.
Qed.

Lemma alpha_trans_rename_right u v b'' s'' s ren sigma :
  b'' = fresh2 sigma v ->
  Alpha ((s, s'')::ren) u v ->
  Alpha ((s, b'')::ren) u (rename s'' b'' v).
Proof.
  intros.
  eapply @alpha_trans with (ren' := ((s'', b'')::nil) ++ (ctx_id_right ren)); eauto.
  - apply alpha_trans_cons. apply id_right_trans.
  - apply alpha_extend_ids_right; [apply ctx_id_right_is_id |].
    apply alphaRename.
    now apply fresh2_over_tv_term in H.
Qed.

Lemma alpha_trans_rename_left u v b' s' s ren sigma :
  b' = fresh2 sigma u ->
  Alpha ((s', s)::ren) u v ->
  Alpha ((b', s)::ren) (rename s' b' u) v.
Proof.
  intros.
  eapply @alpha_trans with (ren := ((b', s')::nil) ++ (ctx_id_left ren)); eauto.
  - apply alpha_trans_cons. apply id_left_trans.
  - apply alpha_extend_ids_right; [apply ctx_id_left_is_id |].
    eapply alpha_sym; [repeat constructor|].
    apply alphaRename.
    now apply fresh2_over_tv_term in H.
Qed.

(* alpha contexts and renaming contexts work the same with shadowing, so this holds
  e.g. if R = (x, y)::(x, z), then mren will rename x to y.
  Also Alpha (x, y)::(x, z) x y holds
  Since the rhs of R can never occur in s, we know that also then z cannot occur in (mren R s)
*)
Lemma alpha_mren (R : list (string * string)) s :
  (* x' can be equal to x., but then x=x' not in s, so the renaming doesnt do anything. *)
  (forall x, In x (map snd R) -> ~ In x (ftv s)) -> Alpha R s (mren R s).
Proof.
Admitted.


(* what we want is:
Suppose   s = (x, y)
Suppose R = (x, y), then that is problematic of course (the y is already present)
But, if R is extended with (y, yfr), then this is no longer problematic.
In other words we need:
forall x, In x (map snd R) AND  In fst s  ->  Either: it is later somewhere in (fst R), i.e.: it gets fixed away

Thought experiment:
what if it gets fixed away to some other free var in s? Then it has to do this formula again, and needs to get fixed away again
Because it is folding over the structure, at some point it needs to be translated to something not in the ftvs

ok. What about
s = (x, y)
R = (x, y), (y, x)
should not be problematic. But why/how to encode this?


Hmm. I guess we could make sure that forall ftvs in s (in the original problem), we have a renaming in R (can be identity)
Then we can rename every ftv at the end of R to something fresh => then we can never have "capture"
*)
Lemma alpha_mren_hmm (R : list (string * string)) s :
  (* x' can be equal to x., but then x=x' not in s, so the renaming doesnt do anything. *)
  (forall x, In x (map snd R) -> ~ In x (ftv s)) -> Alpha R s (mren R s).
Proof.
Admitted.

(* Renamings can be faulty if we rename to something (say y) and y already occured in the term
  this inductive makes sure that when this occurs the "original" y also gets renamed to something unproblematic
*)
Inductive Nice : (list (string * string)) -> term -> Prop :=
  | NiceNil t : Nice nil t

  (* If we rename something to y, and that already occured in t, then we need to rename that away thereafter*)
  | NiceOne x y t R :  ~ In y (btv t) ->   In y (ftv t) -> In y (map fst R) -> Nice R t -> Nice ((x, y)::R) t
  | NiceTwo x y t R : ~ In y (btv t) -> ~ In y (ftv t) ->                     Nice R t -> Nice ((x, y)::R) t. (* Not a problematic renaming*)
(* for non-problematic renamings it can also not be in a bound type variable:
  look at R = (x, y) and t = (tmlam y. x).
*)

(*
  If R is nice, then the renaming is capture-avoiding.

  Forall R, we can create R' which is Nice by extending R with renaming all ftvs to fresh vars, that is the key here
  Also, if we extend R with identity substitutions, we can thereafter still do the extending by freshes.
  If already (x, y), (y, x) in R. And we extend with (x, xfr), (y, yfr), then this does nothing (shadowed)
  but what it does do is have an easy way of always knowing the renaming will be ok: we are playing on the safe side
*)

(* oooof.. Nice allows R = (x, y) and s = tmlam y. x y. Problem is that the rhs is a btv there.
  I think an "easy" fix is to assume nothing in rhs R appears in btv of s.
  I have nwo put this into nice
 *)