
From PlutusCert Require Import STLC_named alpha alpha_ctx_sub Util.List freshness util alpha_rename.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Program.Equality.



(* Suppose In x' (ftv s'), then L x' s'*)

Lemma alphavar_contradiction_shadow' {x x0 y g : string} {ren1 ren2} :
  x0 <> x -> ~ In x (map fst ren1) -> AlphaVar ren2 x y -> AlphaVar (((x0, y)::ren1) ++ ren2) x g -> False.
Proof with try contradiction.
  intros.
  induction ren2.
  - inversion H2; subst...
    inversion H1; subst... (* contradiction: y notin fst ren1, but AlphaVar ren1 y g with y <> g*) admit.

  - destruct a.
    inversion H1; subst.
    + inversion H2; subst...
      (* By x notin fst ren1, we know that AlphaVar ren1 ++ (x, y):: ren2) x g implies
        AlphaVar (x, y)::ren2 x g. But y <> g. contradiction.
      *)
      admit.
    + inversion H2; subst...
      (*
        From AlphaVar ren1 ++ (s, s0)::ren2 x g we know (s, s0)::ren2 x g. Then alphavar unique says y = g, contradiction.
        *)
Admitted.

Lemma alphavar_contradiction_shadow {x x0 y g : string} {ren} :
  x0 <> x -> AlphaVar ren x y -> AlphaVar ((x0, y)::ren) x g -> False.
Proof with try contradiction.
  intros.
  induction ren.
  - inversion H1; subst...
    apply (alphavar_unique_right H0) in H9...
  - destruct a.
    inversion H0; subst.
    + inversion H1; subst...
      inversion H9; subst...
    + inversion H1; subst...
      inversion H12; subst...
      eapply IHren; eauto.
      apply alpha_var_diff; assumption.
Qed.


(* If x in ftv s, then there exists no s' for this context*)
Lemma uhm3 (x x0 z y : string) s s' ren1 ren2 :
    x0 <> x -> ~ In x (map fst ren1) -> In x (ftv s) -> AlphaVar ren2 x y -> Alpha ((x0, y)::ren1 ++ ren2) s s' -> False.
Proof.
    intros.
    generalize dependent x0.
    generalize dependent ren1.
    generalize dependent ren2.
    generalize dependent s'.
    induction s; intros s' ren2 Hxy ren1 Hxnotren1 x0 Hx0notx Halpha.
    - inversion Halpha; subst.
      unfold ftv in H1. apply in_inv in H1; destruct H1; try contradiction; subst.
      apply (alphavar_contradiction_shadow' Hx0notx Hxnotren1 Hxy H2).

    - inversion Halpha; subst.
      assert (x <> s).
      {
        intros Hcontra; subst.
        apply ftv_lam_no_binder in H1.
        contradiction.
      } 
      apply ftv_lam_helper in H1.
      (* Suppose y0 = y. Then we can use IHs with x1 = s and ren3 = (x0, y)::ren1 and ren0 = ren2
      
        Suppose now y0 <> y. Also s <> x0. ??? no we dont know that. Nooo... so we cant do swap.

        So we need to extend it with a prepending of (a, b), where a <> x and b <> y...
      *)
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
  intros Hnotin Halphas Halphax.
  induction Halphas; simpl in *; auto.
  - intros Hcontra.
    destruct Hcontra; [|contradiction].
    subst.
    assert (x0 <> x).
    {
      intros Hcontra.
      subst.
      contradiction Hnotin.
      left.
      reflexivity.
    }
    
    apply (alphavar_unique_not_left H a) in Halphax.
    contradiction.
  - destr_eqb_eq x' y.
    + apply remove_In.
    + assert (Hnotin' : ~ In x' (ftv s2)).
      {
        eapply IHHalphas.
        - unfold not in Hnotin.
          intros Hcontra.
          apply Hnotin.
          right.
          assumption.
        - assert (x0 <> x).
          {
            intros Hcontra.
            subst.
            unfold not in Hnotin.
            apply Hnotin.
            left.
            reflexivity.
          }
          eapply alpha_var_diff; eauto.
          
      }
      rewrite <- Util.List.in_remove.
      intros Hcontra.
      destruct Hcontra; contradiction.
  - 
    apply not_in_app in Hnotin as [Hnotin1 Hnotin2].
    apply not_in_app.
    split.
    + eapply IHHalphas1; eauto.
    + eapply IHHalphas2; eauto.
Qed.

Lemma alpha_preserves_ftv_tv_right {x x' s s' ren} :
  ~ In x' (tv s') ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  ~ In x (ftv s).
Proof.
          (* Bunch of symmetry stuff
          remember (sym_alpha_ctx ren12) as ren12'.
          assert (Halphay': Alpha ren12 (tmvar y1) (tmvar y2)).
          {
            apply alpha_var; assumption.
          }
          eapply @alpha_sym with (ren' := ren12') in Halphay'; [| rewrite Heqren12'; apply sym_alpha_ctx_is_sym].
          assert (Halphay'' : AlphaVar ren12' y2 y1).
          {
            inversion Halphay'.
            assumption.
          }
          eapply @alpha_sym with (ren' := ren12') in Halphas12; [| rewrite Heqren12'; apply sym_alpha_ctx_is_sym].


          eapply @alpha_preserves_ftv with (s := t0); eauto. *)
Admitted.

Lemma no_ftv_subs_helper' y s s' s'' sigma ren ren1 ren2 :
  αCtxTrans ren1 ren2 ren ->
  ~ In y (tv s) ->
  ~ In y (tv_keys_env sigma) ->
  αCtxSub ren sigma sigma ->
  AlphaVar ren y y ->
  Alpha ren1 s s' ->
  Alpha ren2 s' s'' ->
  ~ In y (ftv (sigma [[s'']])).
Proof.
  intros.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent s.
  generalize dependent s''.
  induction s'; intros s'' s_ Hynots ren2 Halphas2 ren1 Halphas1 ren Htrans Hctx Halphay.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    assert (Halphax0y1: AlphaVar ren x y1).
    {
      eapply alpha_var_trans; eauto.
    }
    assert (Hynotx0: y <> x).
    {
      intros Hcontra.
      subst.
      unfold tv in Hynots.
      contradiction Hynots.
      apply in_eq.
    }
    destruct (lookup y1 sigma) eqn:Hlookup.
    {
      assert (In (y1, t) sigma).
      {
        apply lookup_some_then_in in Hlookup.
        assumption.
      }
      intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      assert (In y (tv_keys_env sigma)).
      {
        
        eapply in_tv_value_then_in_tv_keys_env; eauto.
      }
      contradiction.
    }
    {
      simpl.

      destr_eqb_eq y1 y.
      - assert (Hx0y: y = x).
        {
          
          eapply alphavar_unique_right.
          - assert (Alpha ren (tmvar y) (tmvar y)).
            {
              apply alpha_var.
              assumption.
            }
            eapply alpha_sym in H.
            + inversion H.
              exact H5.
            + eapply sym_alpha_ctx_is_sym.
          - assert (Alpha ren (tmvar x) (tmvar y)).
          {
            apply alpha_var.
            assumption.
          }
          eapply alpha_sym in H.
          + inversion H.
            exact H5.
          + eapply sym_alpha_ctx_is_sym.
        }
        contradiction.
      - intros Hcontra.
        destruct Hcontra; contradiction.
    }
    
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    assert (Hnotys0: ~ In y (tv s1)).
    {
      simpl in Hynots.
      auto.
    } 
    rewrite capms_equation_2.
    simpl.
    subst.
    remember (fresh2 _ _) as b.

    (* If y = b, we are done by how remove works*)
    destr_eqb_eq y b.
    remember (fresh2 _ _) as b.
    {
      apply remove_In.
    }
    {
      (* y <> b*)
      rewrite <- Util.List.in_remove.
      intros Hcontra'.
      
      (* We do an unnecessary allowed renaming here, since tv/ftv does not care about this*)
      remember (fresh2 ((y, tmvar y)::sigma) s1) as b'.
      assert (Hnotyreny1b's1: ~ In y (tv (rename x b' s1))).
      {
        apply tv_not_after_rename.
        - apply fresh2_over_key_sigma with (X := y) (s := tmvar y) in Heqb'.
          + auto.
          + apply in_eq.
        - assumption.
      }

      assert (~ In y (ftv (sigma [[rename y1 b s3]]))).
      {
        eapply IHs' with (s := rename x b' s1) (ren := ((b', b)::ren)).
        - assumption.
        - {
          eapply @alpha_trans with (ren' := ((y1, b)::nil) ++ (ctx_id_right ren2)).
          - apply alpha_trans_cons.
            apply id_right_trans.
          - exact H11.
          - apply alpha_extend_ids_right.
            + apply ctx_id_right_is_id.
            + apply alphaRename.
              apply fresh2_over_tv_term in Heqb.
              assumption.
        }
        - eapply @alpha_trans with (ren := ((b', x)::nil) ++ (ctx_id_left ren1)).
          + apply alpha_trans_cons.
            apply id_left_trans.
          + apply alpha_extend_ids_right.
            * apply ctx_id_left_is_id.
            * eapply alpha_sym; [repeat constructor |].
              apply alphaRename.
              apply fresh2_over_tv_term in Heqb'.
              assumption.
          + exact H3.
        - now apply alpha_trans_cons.
        - eapply alpha_ctx_ren_extend_fresh.
          + change ((y, tmvar y):: sigma) with (((y, tmvar y)::nil) ++ sigma) in Heqb'.
            now apply tv_keys_env_helper in Heqb'.
          + change ((y1, tmvar y1):: sigma) with (((y1, tmvar y1)::nil) ++ sigma) in Heqb.
            now apply tv_keys_env_helper in Heqb.
          + assumption.            
        - apply alpha_var_diff.
          + apply fresh2_over_key_sigma with (X := y) (s := tmvar y) in Heqb'.
            * assumption.
            * apply in_eq.
          + auto.
          + assumption.
      }

      destruct Hcontra' as [Hcontra' _].
      contradiction.
    }
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_3.
    simpl.
    intros Hcontra.
    apply in_app_sum in Hcontra.
    simpl in Hynots.
    apply not_in_app in Hynots.
    destruct Hynots as [Hynots1 Hynott1].
    destruct Hcontra.
    + eapply IHs'1 with (s := s1); eauto.
    + eapply IHs'2; eauto.
Qed.

Lemma no_ftv_subs_helper y s sigma :
  ~ In y (tv s) ->
  ~ In y (tv_keys_env sigma) -> (* should be tv*)
  ~ In y (ftv (sigma [[s]])).
Proof.
  intros.
  eapply (@no_ftv_subs_helper' y s s s sigma nil nil nil); eauto.
  - constructor.
  - apply alpha_ctx_ren_nil.
  - apply alpha_var_refl.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_refl. apply alpha_refl_nil.
Qed.

(* IS THIS STILL USED AND WHAT DOES IT DO? *)
Lemma ftv_sub_helper4 x x' y y' s s' s'' sigma sigma' ren1 ren2 ren :
  αCtxTrans ren1 ren2 ren ->
  αCtxSub ren sigma sigma' ->
  Alpha ren1 s s' ->
  Alpha ren2 s' s'' ->
  AlphaVar ren x x' ->
  AlphaVar ren y y' ->
  In x (ftv s) ->
  ~ In y (tv s) -> (* A free var can ber renamed to a name that is bound, then suddenly it is bound! Cannot happen because it is a capture-avoiding substitution, but adding this condition makes it possible to not need a stronger induciton hypothesis*)
  In y' (ftv (((x', tmvar y')::sigma') [[s'']])).
Proof.
  intros.
  generalize dependent s.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  induction s'; intros ren2 ren1 ren Htrans Hctx Halphax Halphay s'' Hs'' s0 Hs' Hxins Hynotins.
  - inversion Hs''.
    inversion Hs'.
    subst.
    rewrite capms_equation_1.
    simpl.
    assert (x = x1).
    {
      inversion Hxins; [auto | contradiction].
    }
    subst.
    (*
      AlphaVar ren x1 ~ x'. 
      but also
      AlphaVar ren x1 y0.
      Hence x' = y0.
    *)
    assert (x' = y0).
    {
      assert (AlphaVar ren x1 y0).
      {
        eapply alpha_var_trans; eauto.
      }
      apply (alphavar_unique_right Halphax) in H.
      assumption.
    }
    subst.
    rewrite String.eqb_refl.
    unfold ftv.
    apply in_eq.
  - inversion Hs'.
    inversion Hs''.
    subst. 
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 _ _) as b1.
    assert (x <> x0).
    {
      intros Hcontra.
      subst.
      apply ftv_lam_no_binder in Hxins.
      contradiction.
    }
    assert (y <> x0).
    {
      intros Hcontra.
      subst.
      unfold tv in Hynotins. fold tv in Hynotins.
      apply not_in_cons in Hynotins as [Hynotins _].
      contradiction.
    }
    assert (In y' (ftv (((x', tmvar y'):: sigma') [[rename y1 b1 s4]]))).
    {
      
      (* hmm again a rename...

      for s0 we can choose s1. We know x in ftv s1.
      Then we need ren1 |- s1 ~ s'.  => ren1 = (x0, s)::ren1

      So then y in ftv (((x, tmvar y) :: sigma ) [[s'']]).

      we need s' ~ s'' = rename y1 b1 s4.
      We know s' ~ s4 with [s, y1]::ren2.

      Then s' ~ rename y b1 s4 with [s, b1]::ren2.

      Then ren := (x0, b1)::ren

      So do we have AlphaVar (x0, b1)::ren x x'? => x <> x0. b1 <> x', so yes.
      Do we have AlphaVar (x0, b1)::ren y y'? => y' <> b1. But what if y = x0? Then y notin ftv (tmlam x0 t s1). 
      Fixed by new condition on y.

    αCtxSub (x0, b1)::ren sigma sigma' ? We already have αCtxSub ren sigma sigma'.
    We for sure do not have that, since x0 not fresh. So it could shadow something.
    But I think we can cheat it, by doing an unncessesary renaming of x0 to fresh2 ((x0, tmvar x0))::sigma) ?.
      
      *)
      remember (fresh2 ((x0, tmvar y)::sigma) s1) as b2.

      assert (In x (ftv s1)).
      {
        apply ftv_lam_helper in Hxins.
        assumption.
      }

      eapply IHs'.
      - apply alpha_trans_cons. exact Htrans.
      - eapply extend_alpha_ctx_fresh.
        + change ((x0, tmvar y) :: sigma) with (((x0, tmvar y)::nil) ++ sigma) in Heqb2.
          exact Heqb2.
        + change ((y1, tmvar y1)::(x', tmvar y') :: sigma') with (((y1, tmvar y1)::(x', tmvar y')::nil) ++ sigma') in Heqb1.
          exact Heqb1.
        + assumption.
      - apply alpha_var_diff.
        + apply fresh2_over_tv_term in Heqb2.
          
          apply extend_ftv_to_tv in H1.
          intros Hcontra.
          subst.
          contradiction.
        + eapply fresh2_over_key_sigma in Heqb1.
          * eauto.
          * apply in_cons. apply in_eq.
        + assumption.
      - (* 
          y not b2 by cheat b2!
          y' notin b1.
        *)
        apply alpha_var_diff; auto.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y) in Heqb2; eauto.
          * simpl in Heqb2.
            auto.
          * apply in_eq.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y') in Heqb1; eauto.
          * simpl in Heqb1.
            auto.
          * apply in_cons. apply in_eq.
      - eapply @alpha_trans with (ren' := (((y1, b1)::nil) ++ ctx_id_right ren2)).
        + apply alpha_trans_cons.
          apply id_right_trans.
        + exact H10.
        + apply alpha_extend_ids_right.
          * apply ctx_id_right_is_id.
          * apply alphaRename.
            apply fresh2_over_tv_term in Heqb1.
            assumption.
      - eapply @alpha_trans with (ren := (((b2, x0)::nil) ++ ctx_id_left ren1)).
        + apply alpha_trans_cons.
          apply id_left_trans.
        + apply alpha_extend_ids_right.
          * apply ctx_id_left_is_id.
          * eapply alpha_sym; [repeat constructor |].
            apply alphaRename.
            apply fresh2_over_tv_term in Heqb2.
            exact Heqb2.
        + exact H2.

      - apply ftv_rename_vacuous_helper; assumption.
      - apply tv_not_after_rename.
        + eapply fresh2_over_tv_value_sigma with (s := tmvar y) in Heqb2; auto.
          * simpl in Heqb2.
            auto.
          * apply in_eq.
        + simpl in Hynotins.
          auto.
    }
    (* y' <> b1 so we can remove the remove *)
    apply Util.List.in_remove.
    split.
    + assumption.
    + eapply fresh2_over_tv_value_sigma with (s := tmvar y') in Heqb1; eauto.
      * simpl in Heqb1.
        auto.
      * apply in_cons. apply in_eq.
  - inversion Hs'.
    inversion Hs''.
    subst.
    rewrite capms_equation_3.
    simpl.
    simpl in Hynotins.
    apply not_in_app in Hynotins.
    destruct Hynotins as [Hynotins1 Hynotint1].

    apply in_app_iff.
    simpl in Hxins.
    apply in_app_sum in Hxins.
    destruct Hxins.
    + left.
      eapply IHs'1; eauto.
    + right.
      eapply IHs'2; eauto.
Qed.

  (* 
    Can there be a ftv in t that is equal to g2, then there is a problem?
    Suppose there is.
    Then this must be in the keys of sigma:
      - if it was not in the keys of sigma, it would still be in sigma [[t]]
      - so then it could not be equal to g2.
    .
    Since we also freshen over sigma, and thus over the keys of sigma,
    it can still not be equal to g2.
  *)
Lemma fresh2_subst_helper { Y sigma t } :
  ~ In Y (tv (sigma [[t]])) -> ~ In Y (tv_keys_env sigma) -> ~ In Y (ftv t).
Proof.
  intros.
  generalize dependent sigma.
  induction t; intros.
  - rewrite capms_equation_1 in H.
    destruct (lookup s sigma) eqn:Hlookup.
    + apply lookup_some_then_in in Hlookup.
      (* s in sigma. Y notin sigma => Y notin s.*)
      admit.
    + intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
  - (* If we can show Y notin ftv t0: Done*)
    rewrite capms_equation_2 in H. 
    remember (fresh2 _ _) as g.
    assert (~ In Y (tv ((sigma [[rename s g t0]])))) by admit.
    (*

    If s = Y, we are donel. Hence assume s <> Y
    notin Y (tv (tmlam g t sigma (rename s g t0)))
    Hence Y <> g.

    notin Y (tv sigma [[rename s g t0]])
    notin Y (tv (s, g)::sigma [[t0]])

    Do we have Y notin tv_keys_env (s,g)::sigma, yes!

    Ok, so for this we need ren sub compose! But do we not need this in ren sub compose by any chance?
    *)

Admitted.