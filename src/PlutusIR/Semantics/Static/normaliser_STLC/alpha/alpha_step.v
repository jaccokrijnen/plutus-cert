From PlutusCert Require Import alpha step alpha_sub STLC_named alpha_ctx_sub freshness util alpha_freshness Util.List.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

(* TODO: Probably need to prove this with strenghtened induction (non-empty context) for the lambda case *)
Lemma step_preserves_alpha {s} {s'} {t} ren :
  Alpha ren s t -> step s s' -> {t' & prod (step t t') (Alpha ren s' t')}.
Proof.
  intros Halpha Hstep.
  generalize dependent t.
  generalize dependent ren.
  induction Hstep; intros ren t0 Halpha; inversion Halpha; subst.
  - inversion H2. subst. 
    eexists.
    split.
    + apply step_beta.
    + now apply alpha_rename_binder.
  - specialize (IHHstep ren s3 H2).
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    eexists (tmapp t' t2).
    split; constructor; assumption.
  - specialize (IHHstep ren t4 H4).
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    eexists.
    split.
    + apply step_appR. exact IHHstep.
    + apply alpha_app; assumption.
  - specialize (IHHstep ((x, y)::ren) s3 H4).
    destruct IHHstep as [t' [IHHstep IHHalpha] ].
    exists (tmlam y A t').
    split.
    + apply step_abs.
      assumption.
    + apply alpha_lam.
      assumption.
Qed.

Lemma red_preserves_alpha {s} {s'} {t} ren :
  Alpha ren s t -> red s s' -> {t' & prod (red t t') (Alpha ren s' t')}.
Proof.
  intros Halpha Hred.
  induction Hred.
  + exists t. split; auto.
    apply starR.
  + destruct IHHred as [t'y [Hredt'y Halphat'y] ].
    apply (step_preserves_alpha ren Halphat'y) in e.
    destruct e as [t'z [Hstept'z Halphat'z] ].
    exists t'z.
    split; auto.
    eapply starSE with (y := t'y); eauto.
Qed.

(*
What if we have (\x. y) (z). Then z in the ftv of the term, but after stepping it is not anymore.
So ftvs can be removed. But they can never be added.
*)
Lemma step_preserves_no_ftv {s s' x} :
  ~ In x (tv s) -> step s s' -> ~ In x (ftv s').
Proof.
  intros Hnotins Hstep.
  induction Hstep.
  - assert (Hxot: ~ In x (tv t)).
    {
      simpl in Hnotins.
      apply de_morgan2 in Hnotins as [_ H].
      now apply not_in_app in H.
    }
    
    destr_eqb_eq x x0.
    + apply fresh2_subst_helper3.
      intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
    + apply no_ftv_subs_helper.
      * simpl in Hnotins.
        apply de_morgan2 in Hnotins as [_ Hnotins].
        now apply not_in_app in Hnotins.
      * simpl.
        intros Hcontra.
        destruct Hcontra; [intuition|].
        rewrite app_nil_r in H0.
        contradiction.
  - simpl in Hnotins.
    rewrite not_in_app in Hnotins.
    destruct Hnotins as [Hnotins1 Hnotint].
    apply IHHstep in Hnotins1.
    simpl.
    apply not_in_app.
    split.
    + assumption.
    + intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
  - simpl in Hnotins.
    rewrite not_in_app in Hnotins.
    destruct Hnotins as [Hnotins1 Hnotint].
    apply IHHstep in Hnotint.
    simpl.
    apply not_in_app.
    split.
    + intros Hcontra.
      apply extend_ftv_to_tv in Hcontra.
      contradiction.
    + assumption.
  - simpl in Hnotins.
    simpl.
    rewrite <- Util.List.in_remove.
    apply de_morgan2 in Hnotins as [x0notx Hxnotins1].
    unfold not.
    intros.
    destruct H as [H _].
    apply IHHstep in Hxnotins1.
    contradiction.
Qed. 

(* Why do we need this up to alpha equivalence?

  Because sub lemmas are up to alpha equivalence.
*)
Lemma step_subst {s t} : 
  step s t -> forall sigma : list (string * term), {alphaSigmaT : term & 
  prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))} .
Proof.
  intros Hstep. induction Hstep; intros sigma.
  - rewrite capms_equation_3.
    rewrite capms_equation_2. simpl.
    remember (fresh2 ((x, tmvar x)::sigma) s) as x'.
    eexists.
    split.
    + eapply step_beta.
    + 
    {
      eapply alpha_trans; eauto.
      - apply alpha_trans_nil.
      - eapply subs_preserves_alpha.
        + apply alpha_ctx_ren_nil.
        + eapply ren_sub_compose_instantiated; eauto.
      - eapply alpha_trans.
        + apply alpha_trans_nil.
        + eapply merge_sub.
          * change ((x, tmvar x)::sigma) with (((x, tmvar x)::nil) ++ sigma) in Heqx'.
            exact Heqx'.
        + eapply commute_sub.
    }
  - (* Left application *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    exists (tmapp (alphaSigmaS2) (sigma [[t]])).
    split.
    + rewrite capms_equation_3.
      apply step_appL.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * assumption.
      * apply alpha_refl.
        apply alpha_refl_nil.
  - (* Right applicaiton *)
    specialize (IHHstep sigma).
    destruct IHHstep as [alphaSigmaT2  [Ht2Step Ht2Alpha] ].
    exists (tmapp (sigma [[s]]) alphaSigmaT2).
    split.
    + rewrite capms_equation_3.
      apply step_appR.
      assumption.
    + rewrite capms_equation_3.
      apply alpha_app.
      * apply alpha_refl.
        apply alpha_refl_nil.
      * assumption.
  - remember (fresh2 ((x, tmvar x)::sigma) s1) as x'.
    specialize (IHHstep ((x, tmvar x')::sigma)).
    destruct IHHstep as [alphaSigmaS2  [Hs2Step Hs2Alpha]  ].
    assert (HalphaRenCompose: nil ⊢ (sigma [[rename x x' s1]]) ~ ((x, tmvar x')::sigma) [[s1]]).
    {
      eapply ren_sub_compose_instantiated; eauto.
    }
    assert( {alphaSigmaT : term & prod (step (sigma [[rename x x' s1]]) alphaSigmaT) (Alpha [] alphaSigmaS2 alphaSigmaT )}).
    {
      eapply step_preserves_alpha.
      - eapply alpha_sym.
        + apply alpha_sym_nil.
        + exact HalphaRenCompose.
      - exact Hs2Step.
    }
    destruct H as [alphaSigmaT [HalphaStep HalphaSigmaT] ].
    eexists.
    split. 
    + rewrite capms_equation_2. simpl.
      rewrite <- Heqx'.
      apply step_abs.
      exact HalphaStep.
    + rewrite capms_equation_2. simpl.

      remember (fresh2 ((x, tmvar x)::sigma) s2) as s0'.
      apply alpha_lam.
      assert (Alpha nil alphaSigmaT (((x, tmvar x')::sigma) [[s2]])).
      {
        eapply alpha_trans; eauto.
        - apply alpha_trans_nil.
        - eapply alpha_sym; eauto.
          + apply alpha_sym_nil.
      }
      eapply alpha_trans.
      * apply id_left_trans.
      * eapply alpha_ids.
        apply ctx_id_left_is_id.
      * eapply alpha_trans.
        -- apply id_left_trans.
        -- change (ctx_id_left [(x', s0')]) with (nil ++ (ctx_id_left [(x', s0')])).
           apply alpha_extend_ids_right.
           ++ apply ctx_id_left_is_id.
           ++ exact H.
        -- eapply alpha_trans.
           ++ apply id_right_trans.
           ++ eapply subs_preserves_alpha.
              ** apply alpha_ctx_cons.
                 apply alpha_var_diff.
                 --- eapply fresh2_over_key_sigma with (X := x) (s := tmvar x) in Heqx'; eauto with *.
                 --- eapply fresh2_over_key_sigma with (X := x) (s := tmvar x) in Heqs0'; eauto with *.
                 --- apply alpha_var_refl.
                 --- apply alpha_var.
                     apply alpha_var_cons.
                     +++ reflexivity.
                     +++ reflexivity.
              ** 
                  eapply alpha_extend_vacuous_single.
                  --- assert (~ In x' (tv s1)).
                      {
                       eapply fresh2_over_tv_term in Heqx'.
                       intros Hcontra.
                       (* apply extend_ftv_to_tv in Hcontra. *)
                       contradiction. 
                      }
                      apply (step_preserves_no_ftv H0) in Hstep. (* Probably easier to do over tv*)
                      assumption.
                  --- now apply fresh2_over_tv_term in Heqs0'.
            ++ change (ctx_id_right [(x', s0')]) with (nil ++ (ctx_id_right [(x', s0')])).
               apply alpha_extend_ids_right.
               ** apply ctx_id_right_is_id.
               ** eapply alpha_sym; eauto.
                  --- apply alpha_sym_nil.
                  --- eapply ren_sub_compose_instantiated; eauto.
Qed.


Lemma step_subst_sigma sigma {s t} :
  step s t -> {alphaSigmaT : term & prod (step (sigma [[ s ]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof.
  intros Hstep.
  apply step_subst.
  assumption.
Qed.

(* TODO: NOt used???? *)
Lemma red_subst sigma {s} {t} : 
  red s t -> {alphaSigmaT : term & prod (red (sigma [[s]]) alphaSigmaT) (Alpha [] alphaSigmaT (sigma [[t]]))}.
Proof. 
  intros Hred.
  induction Hred. 
  - exists (sigma [[s]]). split.
    + apply starR.
    + apply alpha_refl. constructor.
  - apply (step_subst_sigma sigma) in e.
    destruct e as [alphaSigmaZ [Hstep HalphaZ] ].
    destruct IHHred as [alphaSigmaY [Hred' Halpha] ].
    apply @alpha_sym with (ren' := nil) in Halpha; [|apply alpha_sym_nil].
    apply (step_preserves_alpha nil Halpha) in Hstep.
    destruct Hstep as [alphaSigmaZ' [HstepZ' HalphaZ'] ].
    exists alphaSigmaZ'. split.
    + eapply starSE; eauto.
    + apply @alpha_sym with (ren' := nil) in HalphaZ'; [|apply alpha_sym_nil].
      eapply alpha_trans; eauto.
      apply alpha_trans_nil.
Qed.