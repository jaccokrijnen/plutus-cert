
From PlutusCert Require Import STLC_named alpha alpha_ctx_sub Util.List freshness util alpha_rename.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Coq.Program.Equality.

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
    assert (Hnotys0: ~ In y (tv s1)). (* Cannot be restricted to ftv. What if x = y??*)
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

(* TODO: It would make sense to extend these to ftv assumptions, but the IH is not strong enough in those cases*)
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

Lemma fresh2_subst_helper2' Y' Y'' X s t t' t'' ren1 ren2 ren :
  Alpha ren1 t' t ->
  Alpha ren2 t t'' ->
  AlphaVar ren Y' Y'' ->
  αCtxTrans ren1 ren2 ren ->
  In Y' (ftv t') -> 
  In Y'' (ftv t'') -> (* follows from ftv_preserved_under_alpha *)
  X <> Y'' -> 
  In Y'' (ftv ([X := s] t'')).
Proof.
  intros.
  generalize dependent t'.
  generalize dependent t''.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent ren.
  induction t; intros ren HalphaY ren2 ren1 Htrans t'' Halphat2 Hyftv2 t' Halphat1 Hyftv1.
  - inversion Halphat1; subst.
    inversion Halphat2; subst.
    apply ftv_var in Hyftv2; subst.
    apply ftv_var in Hyftv1; subst.
    rewrite capms_var_single_not; auto.
    unfold ftv. intuition.
  - inversion Halphat1; subst.
    inversion Halphat2; subst.
    rewrite capms_equation_2; simpl.
    remember (fresh2 _ s3) as b1.
    (* What if Y'' is b1
      Y'' in ftv (tmlam y t s3, so y'' in ftv s3 and b1 is built up from s3, so Y'' <> b1
      ???*)
    assert (Y'' <> b1).
    {
      apply ftv_lam_helper in Hyftv2.
      apply fresh2_over_tv_term in Heqb1.
      apply extend_ftv_to_tv in Hyftv2.
      intros Hcontra.
      subst.
      contradiction.
    }
    apply Util.List.in_remove; split; auto.
    eapply IHt.
    + eapply alpha_var_diff with (x := x).
      * intros Hcontra.
        subst.
        apply ftv_lam_no_binder in Hyftv1.
        contradiction.
      * symmetry.
        exact H.
      * exact HalphaY.
    + apply alpha_trans_cons.
      exact Htrans.
    + eapply alpha_trans_rename_right; eauto.
    + eapply ftv_lam_rename_helper in Hyftv2.
      exact Hyftv2.
    + exact H2.
    + apply ftv_lam_helper in Hyftv1.
      assumption.
  - inversion Halphat1; subst.
    inversion Halphat2; subst.
    rewrite capms_equation_3.
    simpl.
    apply in_or_app.
    simpl in Hyftv1.
    apply in_app_or in Hyftv1.
    destruct Hyftv1.
    + left.
      eapply IHt1; eauto.
      eapply alpha_preserves_ftv; eauto.
      eapply alpha_trans; eauto.
    + right.
      eapply IHt2; eauto.
      eapply alpha_preserves_ftv; eauto.
      eapply alpha_trans; eauto.
Qed.

Lemma fresh2_subst_helper2 Y X s t :
  In Y (ftv t) -> X <> Y -> In Y (ftv ([X := s] t)).
Proof.
  intros.
  eapply fresh2_subst_helper2' with (ren1 := nil) (ren2 := nil) (ren := nil); eauto.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - apply alpha_var_refl.
  - apply alpha_trans_nil.
Qed.

(* TODO: extend to multiple substitutions: trivial though ;)*)
Lemma fresh2_subst_helper' {Y X s t} :
  ~ In Y (ftv ([X := s] t)) -> X <> Y -> ~ In Y (ftv t).
Proof.
  intros notInt XnotY.
  intros Hcontra.
  apply (fresh2_subst_helper2 Y X s t Hcontra) in XnotY.
  contradiction.
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
    We use this lemma in commute_subst_stronger, which does not use ren_sub_compose!

    Let's first see why we need this lemma. The lemma is not weird or anthing, but maybe we can bypass it

    *)

Admitted.

Lemma fresh2_subst_helper3' s t X R s' :
  R ⊢ s ~ s' ->
  ~ In X (ftv t) -> ~ In X (ftv ([X := t] s')).
Proof.
  intros.
  generalize dependent R.
  generalize dependent s'.
  induction s; intros s' R Halpha.
  - inversion Halpha; subst.
    destr_eqb_eq X y.
    + now rewrite capms_var_helper.
    + rewrite capms_var_single_not; auto.
      unfold ftv.
      intros Hcontra.
      inversion Hcontra.
      * intuition.
      * contradiction.
  - inversion Halpha; subst.
    rewrite capms_equation_2; simpl.
    remember (fresh2 _ _) as b.
    rewrite <- Util.List.in_remove. 
    intros Hcontra.
    destruct Hcontra.
    revert H.
    eapply IHs.
    eapply alpha_trans_rename_right; eauto.
  - inversion Halpha; subst.
    autorewrite with capms.
    simpl.
    intros Hcontra.
    apply in_app_or in Hcontra.
    destruct Hcontra.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed. 

Lemma fresh2_subst_helper3 s t X :
  ~ In X (ftv t) -> ~ In X (ftv ([X := t] s)).
Proof.
  eapply fresh2_subst_helper3'.
  apply alpha_refl. apply alpha_refl_nil.
Qed.
