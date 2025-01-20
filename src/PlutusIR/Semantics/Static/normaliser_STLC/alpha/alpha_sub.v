From PlutusCert Require Import Util.List alpha step freshness alpha_freshness alpha_rename rename util alpha_ctx_sub STLC_named.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

(* Most complex lemma up to now (12 nov) that is completely proved and general over arbitrary substitutions! *)
Lemma sub_vacuous' X t sigma sigma' s s' s'' ren ren1 ren2 :
  αCtxSub ren sigma sigma' ->
  αCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ~ In X (ftv s') -> Alpha ren (((X, t)::sigma) [[ s' ]]) (sigma' [[ s'' ]]).
Proof.
  intros HalphaSigma HalphaTrans Halphas1 Halphas2 Hnotins.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  generalize dependent s'.
  generalize dependent s''.
  induction s; intros s'' s' HxnotIns' ren2 Halphas2 ren1 Halphas1 ren HalphaSigma HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_1.
    simpl.
    subst.
    rewrite capms_equation_1.
    simpl.
    destr_eqb_eq X x.
    + apply not_in_cons in HxnotIns' as [xnotx].
      contradiction.
    + (* X <> x *)
      assert (AlphaVar ren x y0).
      {
        eapply alpha_var_trans; eauto.
      }
      destruct (lookup y0 sigma') eqn:y0sigma'.
      * destruct (lookup x sigma) eqn:xsigma.
        -- eapply alpha_ctx_found; eauto.
        -- exfalso.
           apply (alpha_ctx_left_ex HalphaSigma H0) in y0sigma'.
           destruct y0sigma' as [t' [y0sigma' Halpha] ].
           rewrite y0sigma' in xsigma.
           inversion xsigma.
    * destruct (lookup x sigma) eqn:xsigma.
      -- exfalso.
         apply (alpha_ctx_right_ex HalphaSigma H0) in xsigma as [t' [xsigma Halpha] ].
         rewrite xsigma in y0sigma'.
         inversion y0sigma'.
      -- apply alpha_var.
         assumption.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    subst.
    remember (fresh2 ((x, tmvar x) :: (X, t) ::sigma) s1) as s0'.
    remember (fresh2 ((y0, tmvar y0) :: sigma') s4) as s0''.
    apply alpha_lam.
    eapply IHs.
    + destr_eqb_eq X x.
      * remember (fresh2 ((x, tmvar x) :: (x, t) :: sigma) s1) as x'.
        apply ftv_not_in_after_rename.
        apply fresh2_over_key_sigma with (X := x) (s := t) in Heqx'.
        -- auto.
        -- apply in_cons. apply in_eq.
      * assert (~ In X (ftv s1)).
        {
          apply ftv_lam_negative in HxnotIns';
          auto.
        }
        apply ftv_not_in_rename.
        -- apply fresh2_over_key_sigma with (X := X) (s := t) in Heqs0'.
           ++ auto.
           ++ apply in_cons. apply in_eq.
        -- assumption.
    + eapply alpha_trans_rename_right; eauto.
    + eapply alpha_trans_rename_left; eauto.
    + eapply extend_alpha_ctx_fresh.
      * change ((x, tmvar x):: (X, t)::sigma) with (((x, tmvar x)::(X, t)::nil) ++ sigma) in Heqs0'.
        exact Heqs0'.
      * change ((y0, tmvar y0):: sigma') with (((y0, tmvar y0)::nil) ++ sigma') in Heqs0''.
        exact Heqs0''.
      * exact HalphaSigma.
    + apply alpha_trans_cons.
      exact HalphaTrans.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    simpl.
    unfold ftv in HxnotIns'. fold ftv in HxnotIns'.
    apply not_in_app in HxnotIns' as [HxnotIns1 HxnotIns2].
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto.
Qed.

(* Need alpha because the bigger vacuous substitution is used in fresh variable generation *)
Lemma sub_vacuous X t sigma s :
  ~ In X (ftv s) -> Alpha [] (((X, t)::sigma) [[ s ]]) (sigma [[ s ]]).
Proof.
  eapply sub_vacuous'; try apply alpha_refl; try constructor.
  - apply alpha_ctx_ren_nil.
Qed.

Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x sigma , IdSubst sigma -> IdSubst ((x, tmvar x)::sigma).


(* Identity substitutions preserve alpha equivalence *)
(* The identity substitution is in the EL relation *)
Lemma id_subst_alphavar x σ :
  IdSubst σ ->
  tmvar x = σ [[tmvar x]]. 
Proof.
  intros HidSubst.
  rewrite capms_equation_1.
  destruct (lookup x σ) eqn: Hlookup.
  - induction HidSubst.
    + inversion Hlookup.
    + destr_eqb_eq x0 x.
      * simpl in Hlookup.
        rewrite String.eqb_refl in Hlookup.
        inversion Hlookup; subst.
        reflexivity.
      * simpl in Hlookup.
        apply String.eqb_neq in H.
        rewrite H in Hlookup.
        apply IHHidSubst in Hlookup.
        rewrite Hlookup.
        reflexivity.
  - reflexivity.
Qed.

Lemma id_subst_alpha_stronger s σ : forall s' s'' ren ren1 ren2,
  IdSubst σ ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  αCtxTrans ren1 ren2 ren ->
  ren ⊢ s' ~ (σ [[s'']]).
Proof.
  induction s; intros s' s'' ren ren1 ren2 HidSub HalphaS1 HalphaS2 Htrans;
  inversion HalphaS1;
  inversion HalphaS2; subst.
  - rewrite <- (id_subst_alphavar y0 σ HidSub).
    eapply alpha_trans; eauto.
  - autorewrite with capms; simpl.
    remember (fresh2 _ s4) as b2.
    apply alpha_lam.
    eapply IHs; eauto.
    + eapply alpha_trans_rename_right; eauto.
    + now apply alpha_trans_cons.
  - autorewrite with capms.
    apply alpha_app; eauto.
Qed.

Lemma id_subst_alpha s σ :
  IdSubst σ -> nil ⊢ s ~ (σ [[s]]).
Proof.
  intros HidSubst.
  eapply id_subst_alpha_stronger; eauto.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_trans_nil.
Qed.

Lemma sub_vacuous_single X t s :
  ~ In X (ftv s) -> Alpha [] ([X := t] s) s.
Proof.
  intros Hxnotins.
  assert (Alpha nil (nil [[s]]) s).
  {
    eapply alpha_sym. apply alpha_sym_nil.
    apply id_subst_alpha.
    apply id_subst_nil.
  }
  eapply alpha_trans.
  - apply alpha_trans_nil.
  - eapply sub_vacuous; auto.
  - assumption.
Qed.

Lemma subs_preserves_alpha' σ σ' i : forall s s' R1 R2 R,
  αCtxSub R σ σ' ->
  αCtxTrans R1 R2 R ->
  R1 ⊢ s ~ i ->
  R2 ⊢ i ~ s' ->
  R ⊢ σ [[s]] ~ σ' [[s']].
Proof.
  induction i as [xi | xi ? bi | i1 IHi1 i2 IHi2];
  intros s s' R1 R2 R Hctx Htrans Hαs Hαs';
  inversion Hαs as [xs ? ? Hαvs | xs ? ? bs ? ? Hαbs | s1 ? s2 ? ? Hαs1 Hαs2 ]; subst;
  inversion Hαs' as [? xs' ? Hαvs' |? xs' ? ? bs' ? Hαbs' | ? s1' ? s2' ? Hαs1' Hαs2']; subst;
  autorewrite with capms; simpl.
  - (* Case: tmvar *)
    assert (Hαv: AlphaVar R xs xs'). { eapply alpha_var_trans; eauto. }
      
    destruct (lookup xs σ) eqn:xinsigma.
    + apply (alpha_ctx_right_ex Hctx Hαv) in xinsigma as [t' [Hlookupy' Halphat ] ].
      now rewrite Hlookupy'.
    + destruct (lookup xs' σ') eqn:y0insigma'.
      * apply (alpha_ctx_left_ex Hctx Hαv) in y0insigma' as [t' [Hlookupx Halphat ] ].
        now rewrite Hlookupx in xinsigma.
      * now apply alpha_var.
  - (* Case: tmlam *)
    remember (fresh2 _ bs) as b; rewrite cons_to_append in Heqb.
    remember (fresh2 _ bs') as b'; rewrite cons_to_append in Heqb'.
    apply alpha_lam.

    eapply IHbi.
    + apply alpha_ctx_ren_extend_fresh; auto;
      eapply tv_keys_env_helper; eauto.
    + apply alpha_trans_cons; eauto.
    + eapply alpha_trans_rename_left; eauto.
    + eapply alpha_trans_rename_right; eauto.
  - (* Case: tmapp *)
    apply alpha_app.
    + eapply IHi1; eauto.
    + eapply IHi2; eauto.
Qed.

Lemma subs_preserves_alpha sigma sigma' s s' ren :
  αCtxSub ren sigma sigma' ->
  ren ⊢ s ~ s' ->
  Alpha ren (sigma [[s]]) (sigma' [[s']]).
Proof.
  intros.
  apply (@subs_preserves_alpha' sigma  sigma' s s s' (nil ++ ctx_id_left ren) ren ren); auto.
  - apply id_left_trans; auto.
  - apply alpha_extend_ids_right.
    + apply ctx_id_left_is_id.
    + apply alpha_refl. apply alpha_refl_nil.
Qed.

Lemma ren_sub_compose_stronger s σ σ' X X' Y : forall s' s'' ren ren1 ren2,
  αCtxSub ren σ σ' ->
  αCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  AlphaVar ren X X'->
  lt (String.length X) (String.length Y) ->   (* X string contained in Y *)
  ~ In Y (map fst σ) ->
  (~ In Y (tv s')) ->
  AlphaVar ren Y Y ->
  ren ⊢ σ [[rename X Y s']] ~ ((X', tmvar Y)::σ') [[s'']].
Proof. 

  induction s; intros s' s'' ren ren1 ren2 Hctx Htrans Hαs' Hαs'' Hαx Hlength Hykey Hynottv Hαy.
  - inversion Hαs'.
    inversion Hαs''.
    subst.
    assert (AlphaVar ren x y0). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x X.
    + (* x = X, but alphaVar ren X y0, so alphaVar ren x y0. But AlphaVar ren X X', so y0 = X'*)
      unfold rename. unfold mren. simpl. rewrite String.eqb_refl.
      assert (Hy0X': y0 = X'). { eapply alphavar_unique_right; eauto. }
      rewrite capms_equation_1.
      simpl. subst.
      apply lookup_no_key_then_none in Hykey.
      rewrite Hykey.
      rewrite capms_var_helper.
      apply alpha_var.
      assumption.
    + 
      (* x <> X*)
      rewrite ren_vacuous.
      * eapply alpha_trans.
        -- apply id_right_trans.
        -- apply subs_preserves_alpha.
            ++ eauto.
            ++ apply alpha_var; eauto.
        -- eapply alpha_sym.
           ++ eapply sym_alpha_ctx_left_is_sym.
           ++ change (sym_alpha_ctx (ctx_id_right ren)) with (nil ++ (sym_alpha_ctx (ctx_id_right ren))).
              eapply alpha_extend_ids_right.
              ** apply sym_alpha_ctx_preserves_id_ctx.
                 apply ctx_id_right_is_id.
              ** apply sub_vacuous.
                 intros Hcontra.
                 apply ftv_var in Hcontra; subst.
                 apply (alphavar_unique_not_left H0 H) in Hαx.
                 contradiction.
      * intros Hcontra; subst.
        apply (ftv_var) in Hcontra. symmetry in Hcontra. contradiction.
  - inversion Hαs'.
    inversion Hαs''.
    subst.

    destruct (in_dec String.string_dec X (ftv (tmlam x t s1))).
    {
      assert (HXnotx: X <> x).
      {
        intros HContra.
        rewrite HContra in i.
        assert (~ In x (ftv (tmlam x t s1))) by apply ftv_lam_no_binder.
        contradiction.
      }

      rewrite ren_lam; [|assumption].
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 _ (rename X Y s1)) as s0'.
      remember (fresh2 _ s4) as s0''.
      apply alpha_lam.

      assert (In X (ftv s1)).
        {
          apply ftv_lam_helper in i.
          assumption.
        }
      assert (In Y (tv (rename X Y s1))) by (now apply (ftv_tv_rename_helper) with (Y := Y) in H).

      assert (X <> s0').
      {
        clear IHs.
        intros HContra.

        assert (Hlengths0': gt (String.length s0') (String.length Y)).
        {
          unfold fresh2 in Heqs0'.
          assert (gt (String.length s0') (String.length (String.concat "" (tv (rename X Y s1))))).
          {
            (* s0' = "a" ++ concat blablbla tv (rename X Y s1)

              So that is definitely bigger than length s0'.
            *)
            
            admit.
          }
          unfold gt in H1.
          assert ( le (String.length Y)  (String.length (String.concat "" (tv (rename X Y s1))))). 
          { apply length_concat_helper. assumption. }
          unfold gt.
          apply Nat.le_lt_trans with (m := String.length (String.concat "" (tv (rename X Y s1)))); auto.
        }
        rewrite <- HContra in Hlengths0'.
        lia.
      }

      assert (s0' <> Y).
      {
        intros Hcontra; subst.
        symmetry in Hcontra.
        now apply (fresh2_over_tv_term) in Hcontra.
      }

      assert (Y <> x).
      {
        unfold tv in Hynottv.
        rewrite not_in_cons in Hynottv.
        now destruct Hynottv as [HYfresh _].
      }

        rewrite ren_commute; try auto.
        eapply IHs; auto.
        * eapply alpha_ctx_ren_extend_fresh.
          -- change ((x, tmvar x)::σ) with (((x, tmvar x)::nil) ++ σ) in Heqs0'.
             now apply tv_keys_env_helper in Heqs0'.
          -- change ((y0, tmvar y0)::(X', tmvar Y)::σ') with (((y0, tmvar y0)::(X', tmvar Y)::nil) ++ σ') in Heqs0''.
             now apply tv_keys_env_helper in Heqs0''.
          -- assumption.
        * apply alpha_trans_cons. exact Htrans.
        * eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
          -- apply alpha_trans_cons.
            apply id_left_trans.
          -- change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
             apply alpha_extend_ids_right.
             ++ apply ctx_id_left_is_id.
             ++ eapply alpha_sym.
               ** apply alpha_sym_cons. apply alpha_sym_nil.
               ** apply alphaRename. 
                  intros HContra.
                  assert (s0' <> X) by auto.
                  apply (@tv_rename_vacuous_helper _ X Y _ ) in HContra; auto.
                  eapply fresh2_over_tv_term in Heqs0'.
                  contradiction.
            -- exact H2.
        * eapply alpha_trans_rename_right; eauto.
        * apply alpha_var_diff; auto.
          eapply (fresh2_over_key_sigma Heqs0'').
          apply in_cons. apply in_eq.
        * apply tv_not_after_rename; auto.
          apply tv_not_lam in Hynottv; intuition.
        * apply alpha_var_diff; auto.
          apply (fresh2_over_tv_value_sigma) with (X := X') (s := tmvar Y) in Heqs0''.
          -- unfold tv in Heqs0''.
              apply not_in_cons in Heqs0'' as [Hs0''NotY _].
              assumption.
          -- apply in_cons. apply in_eq.
    }
    {
      rewrite ren_vacuous; [|assumption].
      assert (~ In X' (ftv (tmlam y0 t s4))).
      {
        eapply alpha_preserves_no_ftv; eauto.
        eapply alpha_trans; eauto.
      }
      eapply alpha_trans.
      - eapply id_right_trans.
      - eapply subs_preserves_alpha.
        + exact Hctx.
        + eapply alpha_trans; eauto.
      - change (ctx_id_right ren) with (nil ++ ctx_id_right ren).
        apply alpha_extend_ids_right.
        ++ apply ctx_id_right_is_id.
        ++ eapply alpha_sym; eauto; try constructor.
           eapply sub_vacuous.
           assumption.
      
    }
    - inversion Hαs'.
      inversion Hαs''.
      subst.
      unfold rename. unfold mren. fold mren.
      autorewrite with capms.
      apply alpha_app.
      + eapply IHs1; eauto.
        unfold tv in Hynottv. fold tv in Hynottv.
        apply not_in_app in Hynottv as [Hynottv _].
        assumption.
      + eapply IHs2; eauto.
        unfold tv in Hynottv. fold tv in Hynottv.
        apply not_in_app in Hynottv as [_ Hynottv].
        assumption.
Admitted.

Lemma ren_sub_compose_instantiated X Y s sigma :
  Y = (fresh2 ((X, tmvar X)::sigma) s) ->
  nil ⊢ sigma [[rename X Y s]] ~ ((X, tmvar Y)::sigma) [[s]].
Proof.
  intros.
  eapply ren_sub_compose_stronger; eauto; try constructor.
  - apply alpha_ctx_ren_nil.
  - apply alpha_refl. apply alpha_refl_nil.
  - apply alpha_refl. apply alpha_refl_nil.
  - (* X contained in Y, and Y fresh2, so at least longer (by "a" ++), so length X smaller than length Y*) admit.  
  - (* Freshness *) admit.
  - apply fresh2_over_tv_term in H; auto.
Admitted. 

(* We need a legal ren swap because the new binders get in front of the (x, y) in the inductive step of the lambda*)
Lemma alpha_rename_binder_stronger x y s t t' : forall ren1 ren2 ren s' s'' ren_lrs,
  αCtxTrans ren1 ren2 ren_lrs ->
  Alpha ren1 s' s ->
  Alpha ren2 s s'' ->
  Alpha ren t t' ->
  LegalRenSwap ((x, y)::ren) ren_lrs -> 
  Alpha ren ([x := t] s') ([y := t'] s'').
Proof.
  induction s; intros ren1 ren2 ren s' s'' ren_lrs HalphaTrans HalphaS1 HalphaS2 Halphat Hlrs;
  inversion HalphaS1; subst;
  inversion HalphaS2; subst.
  - assert (AlphaVar ((x, y)::ren) x0 y0). 
    { 
      eapply alphavar_swap. 
      - eapply lrs_sym. exact Hlrs.
      - eapply alpha_var_trans; eauto. 
    }
    destr_eqb_eq x0 x.
    {
      inversion H; subst; try contradiction.
      rewrite capms_var_helper.
      rewrite capms_var_helper.
      assumption.
    }
    {
      inversion H; subst; try contradiction.
      rewrite capms_var_single_not; auto.
      rewrite capms_var_single_not; auto.
      apply alpha_var.
      assumption.
    }
  - autorewrite with capms; simpl.
    remember (fresh2 _ s1) as b1.
    remember (fresh2 _ s3) as b2.
    apply alpha_lam.

    eapply IHs.
    + apply alpha_trans_cons.
      exact HalphaTrans.
    + eapply alpha_trans_rename_left; eauto. 
    + eapply alpha_trans_rename_right; eauto.
    + apply alpha_extend_fresh; auto.
      * eapply fresh2_over_tv_value_sigma in Heqb1.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           apply Heqb1 in Hcontra.
           contradiction.
        -- apply in_cons. apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqb2.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           apply Heqb2 in Hcontra.
           contradiction.
        -- apply in_cons. apply in_eq.
    + eapply lrs_trans.
      * {
        apply lrs_start.
        - symmetry. eapply fresh2_over_key_sigma in Heqb1.
          + exact Heqb1.
          + apply in_cons. apply in_eq.
        - symmetry. eapply fresh2_over_key_sigma in Heqb2.
          + exact Heqb2.
          + apply in_cons. apply in_eq.
        - apply legalRenSwap_id.
      }
      * {
        apply lrs_cons.
        assumption.
      }
  - autorewrite with capms; simpl.
    apply alpha_app; eauto.
Qed.

(* If s in x gets renamed to y in s', 
    doing a substitution for x on s corresponds to a substitution for y on s'*)
Lemma alpha_rename_binder {y : string } {s : term} s' x t t' ren:
  Alpha ((x, y)::ren) s s' ->
  Alpha ren t t' ->
  Alpha ren ([x := t] s) ([y := t'] s').
Proof.
  intros Halphas Halphat.
  eapply alpha_rename_binder_stronger; eauto.
  - apply id_right_trans.
  - apply alpha_ids.
    apply ctx_id_right_is_id.
  - apply legalRenSwap_id.
Qed.

Lemma merge_sub_stronger' x2 y1 x4 y2 s3 t sigma2 sigma4 : forall s1 s2 s4 ren ren12 ren24 ren23 ren34,
  Alpha ren12 s1 (((x2, tmvar y2)::sigma2) [[s2]]) ->
  Alpha ren23 s2 s3 ->
  Alpha ren34 s3 s4 ->
  αCtxTrans ren12 ren24 ren ->
  αCtxTrans ren23 ren34 ren24 ->
  αCtxSub ren24 sigma2 sigma4 ->
  AlphaVar ren24 x2 x4 ->
  Alpha ren t t ->
  ~ In y2 (tv_keys_env sigma2) ->
  ~ In y2 (tv s2) ->
  AlphaVar ren12 y1 y2 ->
  Alpha ren ([y1 := t] s1) (((x4, t)::sigma4) [[s4]]).
Proof.
  induction s3; intros s1 s2 s4 ren ren12 ren24 ren23 ren34 Halphas12 Halphas23 Halphas34 Htrans Htrans24 Hctx Halphax Halphat Hy2notsigma2 Hy2nots2 Halphay.
  - inversion Halphas34; subst.
    inversion Halphas23; subst.
    assert (Hxy: AlphaVar ren24 x y). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x x2.
    {
      assert (y = x4). {eapply alphavar_unique_right; eauto. } subst.
      rewrite capms_var_helper.
      rewrite capms_var_helper in Halphas12.
      inversion Halphas12; subst.
      assert (x = y1). { eapply alphavar_unique_left; eauto. } subst. 
      rewrite capms_var_helper.
      assumption.
    }
    {
      assert (y <> x4). { eapply alphavar_unique_not_left; eauto. } subst.
      rewrite capms_equation_1 in Halphas12.
      rewrite (lookup_neq x x2 (tmvar y2) sigma2 H) in Halphas12.
      rewrite capms_equation_1.
      rewrite (lookup_neq y x4 t sigma4 H0).
      destruct (lookup x sigma2) eqn:Hlookupxsigma2.
      {
        (* first get rid of vacuous substitution y1 := t.*)
        eapply @alpha_trans with (ren := nil ++ (ctx_id_left ren)).
        - apply id_left_trans.
        - eapply alpha_extend_ids_right.
          + apply ctx_id_left_is_id.
          + apply sub_vacuous_single.
            eapply @alpha_preserves_ftv_tv_right with (s' := t0); eauto.
            apply not_env_not_val with (t := t0) in Hy2notsigma2; eauto.
            apply (lookup_some_then_in_values x t0 sigma2 Hlookupxsigma2).
        - apply (alpha_ctx_right_ex Hctx Hxy) in Hlookupxsigma2 as [t' [Hlookupy' Halphat'] ].
          rewrite Hlookupy'.
          eapply alpha_trans; eauto.
      }
      {
        eapply @alpha_trans with (ren := ren12) (t := tmvar x); eauto.
        - inversion Halphas12; subst.
          assert (Hy2notx: y2 <> x). {now apply not_in_cons in Hy2nots2 as [Hy2nots2 _]. }
          assert (Hx0noty1: x0 <> y1). { symmetry. apply (alphavar_unique_not_right Hy2notx Halphay H6). }
          rewrite capms_equation_1.
          rewrite (lookup_neq x0 y1 t nil Hx0noty1); simpl.
          exact Halphas12.
        - assert (Hnotlookupy: lookup y sigma4 = None). { eapply alpha_ctx_right_nex; eauto. }
          rewrite Hnotlookupy.
          eapply alpha_trans; eauto.
      }     
    }
  - inversion Halphas23. subst.
    inversion Halphas34. subst.
    rewrite capms_equation_2 in Halphas12.
    simpl in Halphas12.
    inversion Halphas12; subst.
    remember (fresh2 _ s0) as b1.
    rewrite capms_equation_2.
    rewrite capms_equation_2. simpl.
    remember (fresh2 _ s2) as b2.
    remember (fresh2 _ s5) as b3.
    apply alpha_lam.
    eapply IHs3 with (s2 := rename x b1 s0).
    + eapply alpha_trans_rename_left; eauto.
    + eapply alpha_trans_rename_left; eauto. 
    + eapply alpha_trans_rename_right. exact Heqb3. exact H5.
    + apply alpha_trans_cons; eauto.
    + now apply alpha_trans_cons. 
    + apply alpha_ctx_ren_extend_fresh.
      * eapply tv_keys_env_helper.
        change ((x, tmvar x)::(x2, tmvar y2)::sigma2) with (((x, tmvar x)::(x2, tmvar y2)::nil) ++ sigma2) in Heqb1.
        exact Heqb1.
      * change ((y, tmvar y)::(x4, t)::sigma4) with (((y, tmvar y)::(x4, t)::nil) ++ sigma4) in Heqb3.
        eapply tv_keys_env_helper. exact Heqb3.
      * assumption.
    + apply alpha_var_diff.
      * apply fresh2_over_key_sigma with (X := x2) (s := tmvar y2) in Heqb1.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * apply fresh2_over_key_sigma with (X := x4) (s := t) in Heqb3.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * assumption.
    + apply alpha_extend_fresh; auto.
      * eapply fresh2_over_tv_value_sigma in Heqb2.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           generalize dependent Hcontra. 
           exact Heqb2.
        -- apply in_cons. apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqb3.
        -- intros Hcontra.
           apply extend_ftv_to_tv in Hcontra.
           generalize dependent Hcontra. 
           exact Heqb3.
        -- apply in_cons. apply in_eq.
    + assumption. 
    + eapply tv_lam_rename_helper.
      * eapply fresh2_over_key_sigma in Heqb1.
        -- symmetry. exact Heqb1.
        -- apply in_eq.
      * exact Hy2nots2.
    + apply alpha_var_diff; auto.
      * apply fresh2_over_key_sigma with (X := y1) (s := t) in Heqb2.
        -- assumption.
        -- apply in_cons. apply in_eq.
      * apply fresh2_over_tv_value_sigma with (X := x2) (s := tmvar y2) in Heqb1.
        -- intros Hcontra.
           subst.
           unfold tv in Heqb1.
           unfold not in Heqb1.
           assert (In y2 (y2::nil)).
            {
              apply in_eq.
            }
            apply Heqb1 in H.
            contradiction.
        -- apply in_cons. apply in_eq.
  - inversion Halphas23; subst.
    inversion Halphas34; subst.
    rewrite capms_equation_3 in Halphas12.
    simpl in Halphas12.
    inversion Halphas12; subst.
    autorewrite with capms.

    apply alpha_app.
    + eapply IHs3_1 with (s2 := s0); eauto. simpl in Hy2nots2. apply not_in_app in Hy2nots2. intuition.
    + eapply IHs3_2 with (s2 := t1); eauto. simpl in Hy2nots2. apply not_in_app in Hy2nots2. intuition.
Qed.

Lemma merge_sub : forall sigma sigma_ x y s t,
  y = fresh2 (sigma_ ++ sigma) s -> (* TODO: sigma_ is irrelevant, do I have to name it?*)
  nil ⊢ ([y := t] (((x, tmvar y)::sigma) [[s]])) ~ ((x, t)::sigma) [[s]].
Proof.
  intros.
  eapply merge_sub_stronger' with (ren := nil) (ren12 := nil) (ren23 := nil) (ren34 := nil) (s2 := s) (sigma2 := sigma) (x2 := x) (y2 := y); eauto.
  all: try apply alpha_refl; try constructor.
  - apply alpha_ctx_ren_nil.
  - eapply tv_keys_env_helper. eauto.
  - eapply fresh2_over_tv_term. eauto.
Qed.

(* Remove ftv assumptions and instead destruct in var and lam cases *)
(* TODO: Setoid hell 
    Alpha equivalentie definitie veranderen
  *)
Lemma commute_sub_stronger y y' t t' i1 σ σ' : forall s i2 s' R R1 R2 R12 R3,
  αCtxTrans R1 R2 R12 ->
  αCtxTrans R12 R3 R ->
  αCtxSub R σ σ' ->
  Alpha R1 s i1 -> 
  Alpha R2 i1 i2 ->
  Alpha R3 ([y' := t'] i2) s' ->
  AlphaVar R12 y y' ->
  Alpha R12 t t' ->
  Alpha R (((y, σ [[t]])::σ) [[s]]) (σ' [[ s' ]]).
Proof. 
  induction i1 as [x | | ]; intros s_ i2 s' R R1 R2 R12 R3 Htrans Htrans12 Hctx Hαs Hαi Hαs' Hαy Hαt.
  - inversion Hαs; subst.
    inversion Hαi; subst.
    rewrite capms_equation_1 in Hαs'. simpl in Hαs'.
    assert (AlphaVar R12 x0 y0). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x0 y. {
      assert (y0 = y') by apply (alphavar_unique_right H Hαy); subst. 
      rewrite String.eqb_refl in Hαs'.
      rewrite capms_equation_1; simpl. 
      rewrite String.eqb_refl.
      eapply subs_preserves_alpha; auto.
      eapply alpha_trans; eauto.
    }
    {
      assert (y0 <> y') by apply (alphavar_unique_not_left H0 H Hαy).
      eapply @alpha_trans with (ren := nil ++ ctx_id_left R).
      - simpl. apply id_left_trans.
      - apply alpha_extend_ids_right.
        + apply ctx_id_left_is_id.
        + apply sub_vacuous; auto.
          intros Hcontra. 
          apply in_inv in Hcontra; intuition. 
      - rewrite <- String.eqb_neq in H3. 
        rewrite String.eqb_sym in H3.
        rewrite H3 in Hαs'.
        inversion Hαs'; subst.
        apply subs_preserves_alpha; auto.
        eapply alpha_var.
        eapply alpha_var_trans; eauto.
    }

  - inversion Hαi; subst.
    inversion Hαs; subst.
    rewrite capms_equation_2 in Hαs'.
    simpl in Hαs'.
    inversion Hαs'; subst.
    inversion Hαs; subst.
    remember (fresh2 _ s2) as g1.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 _ s1) as g2.
    remember (fresh2 _ s3) as g3.
    
    apply alpha_lam.
    eapply IHi1 with (R12 := ((g2, g1)::R12)).
    + apply alpha_trans_cons.
      eauto.
    + apply alpha_trans_cons.
      eauto.
    + apply alpha_ctx_ren_extend_fresh. 
      * change ((x, tmvar x)::(y, σ [[t]])::σ) with (((x, tmvar x)::(y, σ [[t]])::nil) ++ σ) in Heqg2.
        eapply tv_keys_env_helper; eauto.
      * change ((y1, tmvar y1)::σ') with (((y1, tmvar y1)::nil) ++ σ') in Heqg3.
        eapply tv_keys_env_helper; eauto.
      * assumption. 
    + eapply alpha_trans_rename_left; eauto.
    + eapply alpha_trans_rename_right; eauto.
    + eapply alpha_trans_rename_right; eauto.
    + apply alpha_var_diff.
      * apply fresh2_over_key_sigma with (X := y) (s := σ [[t]]) in Heqg2; auto.
        apply in_cons. apply in_eq.
      * apply fresh2_over_key_sigma with (X := y') (s := t') in Heqg1; auto.
        apply in_cons. apply in_eq.
      * assumption.
    + eapply alpha_extend_fresh.
      * assert (~ In g2 (tv (σ [[t]]))).
        {
          apply fresh2_over_tv_value_sigma with (X := y) (s := σ [[t]]) in Heqg2; auto with *.
        }
        assert (~ In g2 (tv_keys_env σ)).
        {
          change ((x, tmvar x)::(y, σ [[t]])::σ) with (((x, tmvar x)::(y, σ [[t]])::nil) ++ σ) in Heqg2.
          eapply tv_keys_env_helper; eauto.
        }
        apply (fresh2_subst_helper H H0).
      * apply fresh2_over_tv_value_sigma with (X := y') (s := t') in Heqg1; auto.
        -- intros Hcontra. apply extend_ftv_to_tv in Hcontra. contradiction.
        -- apply in_cons. apply in_eq.
      * assumption.
  - inversion Hαi; subst.
    inversion Hαs; subst.
    rewrite capms_equation_3 in Hαs'.
    inversion Hαs'; subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.

    apply alpha_app.
    + eapply IHi1_1 with (R12 := R12); eauto.
    + eapply IHi1_2 with (R12 := R12); eauto.
Qed.

(* Commute subst *)
(* [] ⊢ ((x, sigma [[t]]) :: sigma) [[s]] ~ sigma [[[x := t] s]] *)
Lemma commute_sub x s t sigma :
  Alpha nil (((x, sigma [[t]])::sigma) [[s]]) (sigma [[ [x := t] s]]).
Proof.
    eapply commute_sub_stronger;
      try solve [ constructor 
                | apply alpha_refl; constructor
                | auto ].
    apply alpha_ctx_ren_nil.
Qed.
