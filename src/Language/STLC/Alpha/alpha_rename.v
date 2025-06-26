Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From PlutusCert Require Import STLC Alpha.alpha Util.List variables util.
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
    
      assert (HignoreRename: forall B, rename x x' (@tmabs B x k s0) = @tmabs B x k s0).
      {
        unfold rename.
        subst.
        simpl.
        rewrite String.eqb_refl.
        reflexivity.
      }
      rewrite HignoreRename.
      apply alpha_lam.
      apply alpha_id_shadows_vacuous.
      unfold tv in Hfresh; fold tv in Hfresh.
      apply not_in_cons in Hfresh.
      destruct Hfresh as [_ Hfresh].
      assumption.
    + assert (H1: forall B, rename x x' (@tmabs B s k s0) = @tmabs B s k (rename x x' s0)).
      {
        unfold rename.
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
      
      apply alpha_extend_id.
      * apply IHs.
        (* We know tv (tmabs s t s0) = s :: tv s0*)
        (* Hence we make a superset argument: *)
        unfold tv in Hfresh; fold tv in Hfresh.
        (* if x' notin x :: s, then also x' not in x*)
        apply not_in_cons in Hfresh.
        destruct Hfresh.
        assumption.
      * apply not_break_shadow_cons; try assumption.
        apply not_break_shadow_nil.
  - unfold rename.
    apply alpha_app.
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
    constructor.
Qed.  


(*
 Stronger result where s and s' not syntactically equal
  New idea! Finally work with high-level ideas instead of induction on terms!
*)
Lemma alphaRenameStronger x x' s s' R :
  ~ (In x' (tv s')) -> 
  NotBreakShadowing x R ->
  Alpha R s s' -> Alpha ((x, x')::R) s (rename x x' s').
Proof.
  intros HnotIns' Hshadow Halpha.
  eapply @alpha_trans with (R := (x, x)::R) (R1 := (x, x')::nil ++ ctx_id_right R).
  - apply alpha_trans_cons.
    apply id_right_trans.
  - apply alpha_extend_id; eauto.
  - apply alpha_extend_ids_right with (R := (x, x')::nil).
    + apply ctx_id_right_is_id.
    + now apply alphaRename.
Qed.

Lemma alpha_trans_rename_right u v b'' s'' s R sigma :
  b'' = fresh2 sigma v ->
  Alpha ((s, s'')::R) u v ->
  Alpha ((s, b'')::R) u (rename s'' b'' v).
Proof.
  intros.
  eapply @alpha_trans with (R1 := ((s'', b'')::nil) ++ (ctx_id_right R)); eauto.
  - apply alpha_trans_cons. apply id_right_trans.
  - apply alpha_extend_ids_right; [apply ctx_id_right_is_id |].
    apply alphaRename.
    now apply fresh2_over_tv_term in H.
Qed.

Lemma alpha_trans_rename_left u v b' s' s R sigma :
  b' = fresh2 sigma u ->
  Alpha ((s', s)::R) u v ->
  Alpha ((b', s)::R) (rename s' b' u) v.
Proof.
  intros.
  eapply @alpha_trans with (R := ((b', s')::nil) ++ (ctx_id_left R)); eauto.
  - apply alpha_trans_cons. apply id_left_trans.
  - apply alpha_extend_ids_right; [apply ctx_id_left_is_id |].
    eapply alpha_sym; [repeat constructor|].
    apply alphaRename.
    now apply fresh2_over_tv_term in H.
Qed.
