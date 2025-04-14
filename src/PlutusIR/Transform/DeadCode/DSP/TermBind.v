
From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import BaseKindedness.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import SemanticEquivalence.CompatibilityLemmas.
From PlutusCert Require Import SemanticEquivalence.Auto.
From PlutusCert Require Import SemanticEquivalence.FundamentalProperty.
From PlutusCert Require Import Substitution.
From PlutusCert Require Import Util.Tactics.

From PlutusCert Require Import Multisubstitution.Congruence.
From PlutusCert Require Import Util.List.

Import PlutusNotations.

From PlutusCert Require Import DeadCode.DSP.Lemmas.
From PlutusCert Require Import DeadCode.DSP.BoundVars.
From PlutusCert Require Import Substitution.Free.

Import ListNotations.

Import Utf8_core.


Section CompatibilityLemmas.

Lemma flatten_nil : ∀ A (xs : list (list A)), flatten ([] :: xs) = flatten xs.
Proof.
  intros A xs.
  rewrite <- (map_id ([] :: xs)).
  rewrite flatten_app.
  rewrite map_id.
  rewrite app_nil_r.
  reflexivity.
Qed.


(* The has_type relation considers binding groups all at once

  | T_Let : ∀ ...
        Delta' = flatten (map binds_Delta bs) ++ Delta
      → map_normalise (flatten (map binds_Gamma bs)) bsGn
      → Gamma' = bsGn ++ Gamma
      → (Delta,, Gamma |-oks_nr bs)
      → (Delta',, Gamma' |-+ t : Tn)
      → Delta |-* Tn : Kind_Base
      → Delta,, Gamma |-+ (Let NonRec bs t) : Tn

This lemma does just one binding at a time
*)
Lemma compat_TermBind_typing Δ Γ b x Tb tb Tbn bs t Tn :
  b = TermBind Strict (VarDecl x Tb) tb ->
  Δ |-* Tb : Kind_Base ->
  normalise Tb Tbn ->
  (Δ ,, Γ |-+ tb : Tbn) ->
  (Δ ,, (x, Tbn) :: Γ |-+ (Let NonRec       bs  t) : Tn) ->
  (Δ ,,             Γ |-+ (Let NonRec (b :: bs) t) : Tn).
Proof.
  intros H_eq H_kind_base H_norm H_ty_tb H_ty_let_bs.

  assert (H_b_wf : Δ ,, Γ |-ok_b b). {
    subst b.
    apply W_Term with (Tn := Tbn); auto.
  }

  inversion H_ty_let_bs.
  eapply T_Let with (bsGn := bsGn ++ [(x, Tbn)]).
  - reflexivity.
  - subst b.
    rewrite flatten_app.
    apply MN_snoc; auto.
  - reflexivity.
  - econstructor.
    + assumption.
    + subst b; simpl.
      eapply MN_cons.
        * constructor.
        * exact H_norm.
    + subst b; simpl.
      assumption.
  - subst b; simpl.
    rewrite flatten_nil.
    subst.
    rewrite <- app_assoc.
    assumption.
  - assumption.
Qed.

Lemma compat_nil Δ Γ T t t' :
  LR_logically_approximate Δ Γ           t  t' T ->
  LR_logically_approximate Δ Γ (Let NonRec [] t) t' T.
Proof.
  intros.
  assert (Δ |-* T : Kind_Base). {
    eapply has_type__basekinded.
    destruct H as [H _].
    exact H.
    }
  apply compatibility_LetNonRec_Nil'; assumption.
Qed.

Lemma elim_TermBind_NonRec__approximate Δ Γ t t' Tn b bs x Tb tb :
  b = TermBind Strict (VarDecl x Tb) tb ->

  Δ ,, Γ |-ok_b b ->
  pure_binding Δ Γ b ->
  disjoint (bvb b) (fv t') ->

  forall Δ_b Γ_b,
    Δ_b = binds_Delta b ->
    map_normalise (binds_Gamma b) Γ_b ->
    Δ_b ++ Δ ,, Γ_b ++ Γ |- (Let NonRec       bs  t) ≤ t' : Tn ->
           Δ ,,        Γ |- (Let NonRec (b :: bs) t) ≤ t' : Tn.
Proof.
  intros H_Eqb.
  intros H_wf_b.

  intros H_purebind H_disjoint_b.
  intros Δ_b Γ_b.
  intros H_Δ_b H_norm_Γ_bs.
  intros H_IH_let_bs.

  (* Consider only TermBind*)
  subst b.
  destruct H_purebind as [Tbn' [H_Tb_Tbn' H_pure]].
  (* TODO: postpone this until inversion is needed on H_wf_b *)
  inversion H_wf_b
    as [ ? ? ? ? ? ? Tbn H_Tb_kind H_Tbn H_tb_ty | | ]
  ; subst. clear H_wf_b.
  remember (TermBind Strict (VarDecl x Tb) tb) as b.

  (* map_normalise logic *)
  unfold binds_Gamma, binds_Delta in *; subst.
  assert (Γ_b = [(x, Tbn)]). {
    inversion H_norm_Γ_bs; subst.
    inversion H3; subst.
    f_equal.
    f_equal.
    eauto using normalisation__deterministic.
  }
  subst Γ_b.

  assert (Tbn' = Tbn). {
    eauto using normalisation__deterministic.
  }
  subst Tbn'.


  (* Split IH in typing and evaluation *)
  unfold LR_logically_approximate in H_IH_let_bs.
  destruct H_IH_let_bs as [H_ty_Let [H_ty_t' H_RC]].



  unfold LR_logically_approximate.
  repeat split.

  (** Typing of complete let *)
  -
    eapply compat_TermBind_typing with
      (x := x) (Tbn := Tbn).

    all: subst; auto.

  (** Typing of post-term in smaller Γ *)
  -
    apply strengthen_Γ_cons with (x := x) (Tx := Tbn).   (* need strengthening lemma for removing vars from context that do not occur free *)
    + simpl in H_disjoint_b.
      unfold disjoint in H_disjoint_b.
      inversion H_disjoint_b; subst.
      assumption.
    + subst; assumption.

  (** Related computations*)
  -
  intros k ρ γ γ'.
  intros H_Δ_ρ H_Γ_γ_γ'.

  apply make_RC.

  intros j H_lt_j_k v.

  intros H_let_terminates.

  (* Push substitutions in to get to form Let NonRec _ _*)
  rewrite msubstA_LetNonRec in H_let_terminates.
  rewrite msubst_LetNonRec in H_let_terminates.

  (* Find that we have terminating bindings *)
  inversion H_let_terminates as
    [ | | | | | | | | | | | | | | | | | | | | | ? ? ? ? H_b_bs_terminate | | ].
  subst.
  clear H_let_terminates.

  (* Push substitutions through *)

  rewrite msubstA_BindingsNonRec_cons, msubst_bnr_cons in H_b_bs_terminate.
  rewrite msubstA_TermBind, msubst_TermBind in H_b_bs_terminate.
  inversion H_b_bs_terminate as
    [ | ? ? ? ? k_v vb k_bs ? ? ? ? H_eval_tb H_tb_no_error H_eval_bs | | | | ]. subst.

  (* case E_Let_TermBind *)
  {

    (* Clean up *)
    clear H_b_bs_terminate.

    assert (H_RC_tb :
      RC k Tbn ρ
         (close (msyn1 ρ) γ  tb)
         (close (msyn2 ρ) γ' tb)).
    {
      assert (H_LR_tb : LR_logically_approximate Δ Γ tb tb Tbn).
      { auto using LR_reflexivity. }
      destruct H_LR_tb as [_ [_ H_approx]].
      eauto.
    }

    assert (H_RV_vb : ∃ vb' , RV (k - k_v) Tbn ρ vb vb').
    {
      rewrite RV_RC in H_RC_tb.
      specialize (H_RC_tb k_v ltac:(lia) _ H_eval_tb).
      destruct H_RC_tb as [vb' [_ [_ H_RV_vb_vb']]].
      eauto.
    }

    destruct H_RV_vb as [vb' H_RV_vb].

    remember ((x, vb) :: γ) as γₓ.
    remember ((x, vb') :: γ') as γ'ₓ.

    (** Construct related environments *)
    assert (H_γₓ_γ'ₓ : RG ρ (k - k_v) ((x, Tbn) :: Γ) γₓ γ'ₓ).
    { subst γₓ γ'ₓ.
      eapply RG_cons.
      - eapply RV_monotone.
        + apply H_Δ_ρ.
        + apply H_RV_vb.
        + lia.
      - eapply normalise_to_normal; eauto.
      - admit. (* TODO: from RV *)
      - admit. (* TODO: from RV *)
      - eapply RG_monotone.
        + apply H_Δ_ρ.
        + apply H_Γ_γ_γ'.
        + lia.
    }

    specialize (H_RC (k - k_v) ρ γₓ γ'ₓ H_Δ_ρ H_γₓ_γ'ₓ).
    setoid_rewrite <- close_equation in H_RC.

    (* Pre-term of IH terminates *)
    assert (H_pre : close (msyn1 ρ) γₓ (Let NonRec bs t) =[ k_bs ]=> v).
    {

      rewrite <- close_equation, <- close_bnr_equation in H_eval_bs.

      remember (TermBind Strict (VarDecl x Tb) tb) as b.

      remember (mdrop (btvbs (b :: bs)) (msyn1 ρ)) as ρ1_t.
      remember (mdrop
                  (List.concat (map bvb (msubstA_bnr (msyn1 ρ) bs )))
                  (drop x γ)
               )
        as γ_t.

      assert
      ( H_subst_pre :
        subst x vb
          (Let NonRec
            (close_bnr (msyn1 ρ) (drop x γ) bs)
            (close ρ1_t γ_t t))
        =
        close (msyn1 ρ) γₓ (Let NonRec bs t)
      ).
      {
        subst γ_t.
        unfold close, close_bnr.
        rewrite <- msubst_LetNonRec.
        subst ρ1_t.


        (* TODO, for general bindings, this won't simplify, but we have to
           do a similar thing for the type substitution, factor it out *)
        rewrite (eq_refl : btvbs (b :: bs) = btvb b ++ btvbs bs).
        subst b. simpl.

        rewrite <- msubstA_LetNonRec.

        subst γₓ.
        simpl.
        apply eq_sym.
        apply subst_msubst.

        { admit.
          (*
          tb is well-typed:
            H_tb_ty : Δ,, Γ |-+ tb : Tbn

          γ is well-typed to Γ:
            H_Γ_γ_γ' : RG ρ k Γ γ γ'

          msyn1 ρ is well-kinded to Δ:
            H_Δ_ρ : RD Δ ρ


          we should conclude that
            /[ γ /] (/[[ msyn1 ρ /] tb) is typeable in empty contexts
          by using
            closingA_preserves_typing_1
            closing_preserves_typing_1

          and by preservation
            vb is typable in empty contexts, hence it is closed (typeable_empty__closed)

          using:
            H_eval_tb : <{ /[ γ /] (/[[ msyn1 ρ /] tb) }> =[ k_v ]=> vb

          This should follow from typing and substitution *) }
        {
          assert (k > 0) by lia.
          eauto using RG_env_closed_1.
        }
      }

      rewrite H_subst_pre in H_eval_bs.

      unfold close, close_bnr in *.
      rewrite msubstA_LetNonRec, msubst_LetNonRec in *.
      eauto using eval.
    }

    (* Post-term of IH terminates *)
    assert (H_post : ∃ v' k', close (msyn2 ρ) γ'ₓ t' =[ k' ]=> v' /\
                     RV (k - k_v - k_bs) Tn ρ v v').
    {
      simple eapply RC_to_RV in H_RC; eauto.
      lia.
    }

  assert (x ∉ fv t').
  {
    simpl in H_disjoint_b.
    unfold disjoint in H_disjoint_b.
    rewrite Forall_singleton in H_disjoint_b.
    assumption.
  }

  destruct H_post as [v' [k' [H_t' RV_v_v']]].
  exists v', k'.
  split.
  {
    unfold close in H_t'.
    subst γ'ₓ.
    rewrite msubst_not_in_fv in H_t'.
    - assumption.
    - assert (fv_msubstA : ∀ xs t , fv (msubstA xs t) = fv t) by admit.
      rewrite fv_msubstA.
      assumption.
  }
  {
    assert (k - (k_v + 1 + k_bs) <= k - k_v - k_bs) by lia.
      eapply RV_monotone; eauto.
  }

  }

  (* case E_Error_Let_TermBind *)
  {
    (** Contradiction: tb ⇓ Error, but tb is a safe binding, so
        it should terminate with a value *)
    admit. (* TODO: not sure if this is provable with term substitutions *)
      (*
    unfold pure_open in *.
    assert (normal_Ty Tbn). {eauto using normalise_to_normal. }
    specialize (H_pure ltac:(assumption) ltac:(assumption) (msyn1 ρ) γ).

    assert (H_pure_γ : pure_substitution γ). { apply RG_pure_substitution_1 in H_Γ_γ_γ'. assumption. }
    assert (H_substitution_γ : substitution Γ γ). { apply RG_substitution_1 in H_Γ_γ_γ'. assumption. }

    assert (H_pure_closed : pure (close (msyn1 ρ) γ tb)) by auto.
    destruct H_pure_closed as [l [vb [H_eval H_not_err]]].
    apply eval__deterministic in H_eval.
    unfold P_eval in H_eval.
    apply H_eval in H0 as [H_v_Error _].
    subst vb.
    assert (is_error (Error T')) by constructor.
    contradiction.
    *)
  }

Admitted.

Lemma elim_TermBind_NonRec__approximate_rev Δ Γ t t' Tn b bs x Tb tb :
  b = TermBind Strict (VarDecl x Tb) tb ->

  Δ ,, Γ |-ok_b b ->
  pure_binding Δ Γ b ->
  disjoint (bvb b) (fv t') ->

  forall Δ_b Γ_b,
    Δ_b = binds_Delta b ->
    map_normalise (binds_Gamma b) Γ_b ->
    Δ_b ++ Δ ,, Γ_b ++ Γ |- t' ≤ (Let NonRec       bs  t) : Tn ->
           Δ ,,        Γ |- t' ≤ (Let NonRec (b :: bs) t) : Tn.
Proof.
Admitted.



End CompatibilityLemmas.
