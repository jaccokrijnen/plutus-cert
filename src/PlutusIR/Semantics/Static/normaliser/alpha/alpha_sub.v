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

Lemma alpha_empty_sub s :
Alpha [] (nil [[s]]) s.
Proof.
  induction s.
  - rewrite capms_equation_1.
    simpl.
    apply alpha_var.
    apply alpha_var_refl.
  - rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(s, tmvar s)] s0) as s0'. 
    apply alpha_lam.
    (* Through transitivity and IH we would have to prove:
        [(s0' , s)] |- [] [[rename s s0' s0]] ~ [] [[s0]]
      *)
    (* PFFFF not easy to prove... Probably a corollary of ren_sub_compose_stronger_multiple
      But so trivial, I will believe it as fact! 
     *)
Admitted.

Lemma sub_vacuous_single X t s :
  ~ In X (ftv s) -> Alpha [] ([X := t] s) s.
Proof.
  intros Hxnotins.
  assert (Alpha nil (nil [[s]]) s).
  {
    apply alpha_empty_sub.
  }
  eapply alpha_trans.
  - apply alpha_trans_nil.
  - eapply sub_vacuous; auto.
  - assumption.
Qed.

Lemma sub_vacuous_single_stronger X t s s' ren :
  ~ In X (ftv s) -> Alpha ren s s' -> Alpha ren ([X := t] s) s'.
Proof.
Admitted.

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


Lemma ren_sub_compose_stronger_single : forall s s' s'' ren ren1 ren2 Z Z' t X X' Y,
  αCtxTrans ren1 ren2 ren ->
  ren1 ⊢ s' ~ s ->
  ren2 ⊢ s ~ s'' ->
  ren ⊢ t ~ t ->
  AlphaVar ren X X'->
  AlphaVar ren Z Z' ->
  (* X string contained in Y: *)
  lt (String.length X) (String.length Y) ->
  Z <> Y /\ (~ In Y (tv s')) ->
  In X (ftv s') ->
  AlphaVar ren Y Y ->
  ren ⊢ [Z := t] (rename X Y s') ~ ((X', tmvar Y)::(Z', t)::nil) [[s'']].
Proof. 
  intros s s' s'' ren ren1 ren2 Z Z' t X X' Y Htrans HalphaS1 HalphaS2 Halphat HalphaX HalphaZ Hlength HZnotY  Hftv HalphaY.



  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.

  induction s; intros ren2 ren1 ren HalphaTrans Halphat HalphaVarX HalphaVarZ HalphaVarY s'' Halphas2 s' Halphas1 HYfresh Hftv.
  - inversion Halphas1.
    inversion Halphas2.
    subst.
    assert (AlphaVar ren x y0). {eapply alpha_var_trans; eauto. }
    destr_eqb_eq x X.
    + (* x = X, but alphaVar ren X y0, so alphaVar ren x y0. But AlphaVar ren X X', so y0 = X'*)
      unfold rename. unfold mren. simpl. rewrite String.eqb_refl.
      assert (Hy0X': y0 = X'). { eapply alphavar_unique_right; eauto. }
      rewrite capms_equation_1.
      simpl.
      destruct HYfresh as [HZnotY _].
      rewrite <- String.eqb_neq in HZnotY.
      rewrite HZnotY.
      rewrite capms_equation_1.
      simpl.
      rewrite Hy0X'.
      rewrite String.eqb_refl.
      apply alpha_var.
      assumption.

    + (* x <> X*)
      (* Contradiction: ftv (tmvar x) = x, and then X in x => X = x*)
      exfalso.
      unfold ftv in Hftv.
      apply in_inv in Hftv.
      destruct Hftv.
      * contradiction.
      * contradiction.
  - 
    inversion Halphas1.
   
    inversion Halphas2.
    subst.
    assert (HXnotx: X <> x).
    {
      intros HContra.
      rewrite HContra in Hftv.
      assert (~ In x (ftv (tmlam x t0 s1))) by apply ftv_lam_no_binder.
      contradiction.
    }

      rewrite ren_lam; [|assumption].
      rewrite capms_equation_2.
      rewrite capms_equation_2.
      simpl.
      remember (fresh2 [(x, tmvar x); (Z, t)] (rename X Y s1)) as s0'.
      remember (fresh2 [(y0, tmvar y0);(X', tmvar Y); (Z', t)] s4) as s0''.
      apply alpha_lam.

      assert (In X (ftv s1)).
        {
          apply ftv_lam_helper in Hftv.
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
            admit. (* TODO: Changed fresh2 definition *)
            (* clear Heqs0''.
            rewrite Heqs0'.
            repeat rewrite length_helper.
            change (String.length "a") with 1.
            remember (String.length (String.concat "" (tv (rename X Y s1)))) as n.
            remember (String.length (x, tmvar x).1) as m1.
            remember (String.length (Z, t).1) as m2.
            remember (String.length "") as m3.
            remember (String.length (String.concat "" (flat_map (compose tv snd) [(x, tmvar x); (Z, t)]))) as m4.
            apply Nat.lt_le_trans with (m := 1 + n); auto.
            apply Nat.add_le_mono_l; auto.
            assert (le n (m4 + n)).
            {
              apply Nat.le_add_l.
            }
            assert (le (m4 + n) ((m3 + m2) + (m4 + n))).
            {
              apply Nat.le_add_l.
            }
            assert (le ((m3 + m2) + (m4 + n)) (m1 + ((m3 + m2) + (m4 + n)))).
            {
              apply Nat.le_add_l.
            }
            apply Nat.le_trans with (m := m4 + n); auto.
            apply Nat.le_trans with (m := (m3 + m2) + (m4 + n)); auto.
            rewrite <- Nat.add_assoc.
            rewrite <- Nat.add_assoc in H4.
            rewrite <- Nat.add_assoc.
            rewrite <- Nat.add_assoc.
            assumption. *)
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
        intros Hcontra.
        subst.
        symmetry in Hcontra.


        apply (fresh2_over_tv_term) in Hcontra.
        contradiction.
      }

      assert (Y <> x).
      {
        destruct HYfresh as [_ HYfresh].
        unfold tv in HYfresh.
        rewrite not_in_cons in HYfresh.
        destruct HYfresh as [HYfresh _].
        assumption.
      }

        rewrite ren_commute; try auto.
        eapply IHs.
        * apply alpha_trans_cons. exact HalphaTrans.
        * eapply (fresh2_over_tv_value_sigma) in Heqs0'; eapply (fresh2_over_tv_value_sigma) in Heqs0''.
          -- apply (alpha_not_in_tv_helper); eauto.
          -- apply in_cons. apply in_cons. apply in_eq.
          -- apply in_cons. apply in_eq.
          -- apply in_eq.
        * apply alpha_var_diff.
          -- auto.
          -- 
            eapply (fresh2_over_key_sigma Heqs0'').
            apply in_cons.
            apply in_eq.
          -- assumption.
        
        * apply alpha_var_diff.
          -- eapply (fresh2_over_key_sigma Heqs0').
             apply in_cons.
             apply in_eq.
          -- eapply (fresh2_over_key_sigma Heqs0'').
             apply in_cons.
             apply in_cons.
             apply in_eq.
          -- assumption.
        * apply alpha_var_diff.
           -- assumption.
           -- apply (fresh2_over_tv_value_sigma) with (X := X') (s := tmvar Y) in Heqs0''.
              ++ unfold tv in Heqs0''.
                 apply not_in_cons in Heqs0'' as [Hs0''NotY _].
                 assumption.
              ++ apply in_cons. apply in_eq.
           -- assumption.
      
        * eapply alpha_trans_rename_right; eauto.
        * eapply @alpha_trans with (ren := (s0', x) :: (ctx_id_left ren1)).
          -- apply alpha_trans_cons.
            apply id_left_trans.
          --  
            change ((s0', x) :: (ctx_id_left ren1)) with (((s0', x)::nil) ++ (ctx_id_left ren1)).
              apply alpha_extend_ids_right.
              ++ apply ctx_id_left_is_id.
              ++ eapply alpha_sym.
                ** apply alpha_sym_cons. apply alpha_sym_nil.
                ** apply alphaRename. 
                   (*
                    s0' <> tv (rename X Y s1). now, if we dont do the renaming, we can suddenly have only X extra in there. 
                    But also X <> s0'.
                   *)
                   assert (~ In s0' (tv (rename X Y s1))).
                   {
                    eapply fresh2_over_tv_term; eauto.
                   }

                   intros HContra.
                   clear IHs.
                   assert (s0' <> X).
                   {
                      auto.
                   }
                   apply (@tv_rename_vacuous_helper _ X Y _ (H6)) in HContra.
                   contradiction.
          -- assumption.

          
        * destruct HYfresh as [HZnotY HYfresh].

          split; [assumption|]. 
        
          admit. (* Y not in tv s1? Yes by Y notin tv (tmlam x t0 s1). Also Y <> x and Y <> s0'*)
        * assert (In X (ftv s1)).
        {
          apply ftv_lam_helper in Hftv.
          assumption.
         }
        
          apply (@ftv_rename_vacuous_helper _ x s0' _ HXnotx) in H5.

          assumption.
        
       - admit. 
  

Admitted.

Lemma alpha_rename_binder_stronger x y ren1 ren2 ren s s' s'' t t' :
  αCtxTrans (ren1) ren2 (ren) ->
  Alpha ((x, y)::ren1) s' s ->
  Alpha ren2 s s'' ->
  Alpha ren t t' ->
  In x (ftv s') ->
  In y (ftv s) -> (* I think that follows from the alpha and In x (ftv s')*)
  In y (ftv s'') ->
  Alpha ren ([x := t] s') ([y := t'] s'').
Proof.
  intros HalphaTrans HalphaS1 HalphaS2 Halphat Hinxs' Hinys Hinys''.
  generalize dependent s'.
  generalize dependent s''.
  generalize dependent ren.
  generalize dependent ren1.
  generalize dependent ren2.
  induction s; intros ren2 ren1 ren HalphaTrans Halphat s'' HalphaS2 Hinys'' s' HalphaS1 Hinxs'.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    assert (Hyy1: y = y1).
    {
      unfold ftv in Hinys''.
      apply in_inv in Hinys''.
      destruct Hinys''.
      - symmetry. assumption.
      - contradiction.
    }
    assert (Hxx0: x = x0).
    {
      unfold ftv in Hinxs'.
      apply in_inv in Hinxs'.
      destruct Hinxs'.
      - symmetry. assumption.
      - contradiction.
    }
    subst.
    rewrite capms_equation_1.
    rewrite capms_equation_1.
    simpl.
    rewrite String.eqb_refl.
    rewrite String.eqb_refl.
    assumption.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    rewrite capms_equation_2.
    rewrite capms_equation_2.
    simpl.
    remember (fresh2 [(x0, tmvar x0); (x, t)] s1) as s0'.
    remember (fresh2 [(y1, tmvar y1); (y, t')] s4) as s0''.
    apply alpha_lam.
    assert (Hyins0: In y (ftv s0)).
    {
      apply ftv_lam_helper in Hinys.
      assumption.
    } 
    assert (Hyins'' : In y (ftv (rename y1 s0'' s4))).
    {
      remember Hinys'' as Hinys''copy. clear HeqHinys''copy.
      apply ftv_lam_helper in Hinys''. 
      apply ftv_rename_vacuous_helper.
      - intros Hcontra.
        subst.
        apply ftv_lam_no_binder in Hinys''copy.
        contradiction.
      - assumption.
    }
    assert (Hxins': In x (ftv (rename x0 s0' s1))).
    {
      remember Hinxs' as Hinxs'copy. clear HeqHinxs'copy.
      apply ftv_lam_helper in Hinxs'. 
      apply ftv_rename_vacuous_helper.
      - intros Hcontra.
        subst.
        apply ftv_lam_no_binder in Hinxs'copy.
        contradiction.
      - assumption.
    }

    specialize (IHs Hyins0 ((s, s0'')::ren2) ((s0', s)::ren1)).

    eapply IHs; clear IHs.
    + apply alpha_trans_cons.
      assumption.
    + apply alpha_extend_fresh.
      * eapply fresh2_over_tv_value_sigma in Heqs0'.
        -- eauto. 
          (* TODO: s0' notin tv t => s0' notin ftv t lemma*)
          admit. 
        -- apply in_cons. apply in_eq.
      * eapply fresh2_over_tv_value_sigma in Heqs0''.
        -- eauto. admit.
        -- apply in_cons. apply in_eq.
      * assumption.
    + eapply alpha_trans_rename_right; eauto.
    + assumption.
    + apply alpha_swap with (ren := (s0', s)::(x, y)::ren1).
      * apply lrs_start.
        -- eapply fresh2_over_key_sigma.
           ++ exact Heqs0'.
           ++ apply in_cons. apply in_eq.
        -- intros Hcontra.
           rewrite Hcontra in Hinys.
           apply ftv_lam_no_binder in Hinys.
           contradiction.
        -- apply legalRenSwap_id.
      * eapply alpha_trans_rename_left; eauto.
    + assumption.
  - inversion HalphaS1.
    inversion HalphaS2.
    subst.
    rewrite capms_equation_3.
    rewrite capms_equation_3.
    simpl.
    unfold ftv in Hinxs'.
    (* fold ftv in Hinxs'.
    apply in_app_or_set in Hinxs' as [Hinxs1 | Hinxs2].
    apply alpha_app.
    + eapply IHs1; eauto.
    + eapply IHs2; eauto. *)
Admitted.


(* If s in x gets renamed to y in s', 
    doing a substitution for x on s corresponds to a substitution for y on s'*)
Lemma alpha_rename_binder {y : string } {s : term} s' x t t' ren:
  Alpha ((x, y)::ren) s s' ->
  Alpha ren t t' ->
  Alpha ren ([x := t] s) ([y := t'] s').
Proof.
  intros Halphas Halphat.
  destruct (in_dec String.string_dec x (ftv s)).
  {
    assert (Hinys: In y (ftv s')). {
      apply alpha_in_ftv_helper2 in Halphas; auto.
    }

  eapply alpha_rename_binder_stronger; eauto.
  - apply id_right_trans.
  - change (ctx_id_right ren) with (nil ++ (ctx_id_right ren)). 
    apply alpha_extend_ids_right.
    + apply ctx_id_right_is_id.
    + apply alpha_refl.
      apply alpha_refl_nil.
  }
  {
    assert (Hnotinys: ~ In y (ftv s')). {
      apply alpha_not_in_ftv_helper2 in Halphas.
      - assumption.
      - assumption.
    }

    (* Three ingredients necessary for transitivity result *)
    assert (Alpha nil ([x := t] s) s).
    {
      apply sub_vacuous_single.
      assumption.
    }
    assert (Alpha ren s s').
    {
      apply @weaken_vacuous_alpha with (X' := y) (X := x); assumption.
    }
    assert (Alpha nil s' ([y := t'] s')).
    {
      eapply alpha_sym.
      - apply alpha_sym_nil.
      - apply sub_vacuous_single.
        assumption.
    }

    eapply alpha_trans.
    - apply id_left_trans.
    - apply alpha_extend_ids_right with (idCtx := ctx_id_left ren) in H.
      + exact H.
      + apply ctx_id_left_is_id.
    - eapply alpha_trans.
      + apply id_right_trans.
      + exact H0.
      + apply alpha_extend_ids_right with (idCtx := ctx_id_right ren) in H1.
        * exact H1.
        * apply ctx_id_right_is_id.
  }
Qed.

Lemma ren_sub_compose_instantiated X Y s sigma :
  Y = (fresh2 ((X, tmvar X)::sigma) s) ->
  nil ⊢ sigma [[rename X Y s]] ~ ((X, tmvar Y)::sigma) [[s]].
Proof.
  (* intros HYfresh.
  induction s.
  - admit.
  - rewrite ren_lam; auto.
  destruct (in_dec String.string_dec X (ftv s)).
  {
  (* 
    From HYfresh we can conclude: 
    When we have a term [Z := t] (tmlam x A s) we create a fresh var exactly equal to Y.
    and we know Y not in s, Y not in Z, Y not ini t
    
    ~ (In Y (tv ([Z := t] s))). ???
    and therefore 
  *)
  eapply ren_sub_compose_stronger_single; eauto; try constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - apply alpha_refl. constructor.
  - eapply length_helper; eauto.
  - admit.
  - admit.
  } *)
Admitted. 

(* TODO: GETS STTUCK, SHOW JACCO*)
Lemma subs_preserves_alpha''' sigma sigma' s : forall s' ren,
  αCtxSub ren sigma sigma' ->
  ren ⊢ s ~ s' ->
  Alpha ren (sigma [[s]]) (sigma' [[s']]).
Proof.
  generalize dependent sigma.
  generalize dependent sigma'.
  induction s; 
  intros sigma'_ sigma_ s'_ ren_ Hctx Ha_s;
  inversion Ha_s as [_1 s'' _2 Hav_s2 |_1 s'' _2 _3 s0'' _4 Ha_s02 | _1 sl'' _2 sr'' _3 Ha_sl2 Ha_sr2]; subst.
  - (* Case: tmvar *)
    rewrite capms_equation_1. 
    rewrite capms_equation_1.
    admit.
    (* destruct (lookup s' sigma) eqn:xinsigma.
    + apply (alpha_ctx_right_ex Hctx Havs) in xinsigma as [t' [Hlookupy' Halphat ] ].
      now rewrite Hlookupy'.
    + destruct (lookup s'' sigma') eqn:y0insigma'.
      * apply (alpha_ctx_left_ex Hctx Havs) in y0insigma' as [t' [Hlookupx Halphat ] ].
        now rewrite Hlookupx in xinsigma.
      * now apply alpha_var. *)
  - (* Case: tmlam *)
    rewrite capms_equation_2; simpl.
    rewrite capms_equation_2; simpl.
    remember (fresh2 _ s0) as b.
    remember (fresh2 _ s0'') as b''.
    apply alpha_lam.
    eapply @alpha_trans with (ren := nil ++ (ctx_id_left ((b, b'')::ren_))); eauto.
    + simpl. apply alpha_trans_cons.  apply id_left_trans.
    + apply alpha_extend_ids_right.
      * apply ctx_id_left_is_id.
      * now apply ren_sub_compose_instantiated.
    + {
      eapply @alpha_trans with (t := ((s'', tmvar b'') :: sigma'_) [[s0'']]) (ren := (b, b'')::ren_) (ren' := nil ++ (ctx_id_right ((b, b'')::ren_))); eauto.
      * simpl. apply alpha_trans_cons. apply id_right_trans.
      * assert (Alpha ((b, b'')::(s, s'')::ren_) (((s, tmvar b):: sigma_) [[s0]]) (((s'', tmvar b'') :: sigma'_) [[s0'']])).
      (* {
        apply (@IHs ((s'', tmvar b'')::sigma'_) ((s, tmvar b)::sigma_)).
        - 
      }

         apply (@IHs ((s'', tmvar b'')::sigma'_) ((s, tmvar b)::sigma_)). 
        -- admit.
        -- 
        (*
            Uhm. We know ren_ |- tmlam s t s0 ~ tmlam s'' t s0''.

            Hence we know (s, s'')::ren_  |-  s0 ~ s0''.

          So we cannot use IH, since then ren = ((b, b''):: ren_)
          *)

          admit.
      *  *)
      admit.
      admit.
      all: admit.
      * all: admit.
      
    }
    

Admitted.

Require Import Coq.Program.Equality.

Lemma capms_var_helper x sigma t :
  ((x, t)::sigma) [[tmvar x]] = t.
Admitted.

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
            eapply @alpha_preserves_ftv_right with (s' := t0); eauto.
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

Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x sigma , IdSubst sigma -> IdSubst ((x, tmvar x)::sigma).

Lemma id_subst_preserves_alpha s sigma :
  IdSubst sigma -> nil ⊢ sigma [[s]] ~ s.
Proof.
  (* WE cannot use ren sub compose because no freshness *)
Admitted.

(* Remove ftv assumptions and instead destruct in var and lam cases *)
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
      *  admit. (* fresh *)
      * admit. (* fresh *) 
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
      * assert (~ In g2 (tv (σ [[t]]))) by admit. (* fresh*)
        assert (~ In g2 (tv_keys_env σ)) by admit. (* fresh*)
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
Admitted.

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
