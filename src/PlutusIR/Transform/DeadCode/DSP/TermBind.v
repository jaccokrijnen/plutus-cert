
From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import Transform.DeadCode.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import SemanticEquivalence.CompatibilityLemmas.
From PlutusCert Require Import SemanticEquivalence.Auto.
From PlutusCert Require Import SemanticEquivalence.FundamentalProperty.
From PlutusCert Require Import Analysis.UniqueBinders.
From PlutusCert Require Import Substitution.
From PlutusCert Require Import Util.Tactics.

Import PlutusNotations.

From PlutusCert Require Import DeadCode.DSP.Lemmas.
From PlutusCert Require Import DeadCode.DSP.BoundVars.
From PlutusCert Require Import DeadCode.DSP.SubstitutionNonFree.

Import NamedTerm.
Import ListNotations.
Import UniqueBinders.Term.

Import Utf8_core.

Set Diffs "on".


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
  Δ |-* T : Kind_Base -> (* May not be necessary, see #7 *)
  LR_logically_approximate Δ Γ           t  t' T ->
  LR_logically_approximate Δ Γ (Let NonRec [] t) t' T.
Proof.
  apply compatibility_LetNonRec_Nil'.
Qed.

Lemma compat_TermBind Δ Γ t t' Tn b bs x Tb tb Tbn :
  Δ |-* Tb : Kind_Base ->
  normalise Tb Tbn ->
  (Δ ,, Γ |-+ tb : Tbn) ->

  disjoint (bvb b) (fv t') ->
  unique (Let NonRec (b :: bs) t) ->

  forall Δbs Γbs,
    b = TermBind Strict (VarDecl x Tb) tb ->
    pure_open Δ Γ tb Tbn ->
    Δbs = Δ ->
    Γbs = (x, Tbn) :: Γ ->
    LR_logically_approximate Δbs Γbs (Let NonRec       bs  t) t' Tn ->
    LR_logically_approximate Δ   Γ   (Let NonRec (b :: bs) t) t' Tn.
Proof.
  intros H_Tb_kind H_Tbn H_tb_ty.
  intros H_disjoint_b H_unique.
  intros Δbs Γbs.
  intros H_Eqb H_pure H_Δb H_Γb.
  intros H_IH_let_bs.

  subst b.

  (* Split IH in typing and evaluation *)
  unfold LR_logically_approximate in H_IH_let_bs.
  destruct H_IH_let_bs as [H_ty_Let [H_ty_t' H_RC]].

  unfold LR_logically_approximate.
  repeat split.

  (** Typing of complete let *)
  - eapply compat_TermBind_typing with
      (x := x) (Tbn := Tbn).
    all: subst; auto.

  (** Typing of post-term in smaller Γ *)
  - apply strengthen_Γ with (x := x) (Tx := Tbn).   (* need strengthening lemma for removing vars from context that do not occur free *)
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

  intros j H_lt_j_k e_f.

  intros H_let_terminates.

  (* Push substitutions in to get to form Let NonRec _ _*)
  rewrite msubstA_LetNonRec in H_let_terminates.
  rewrite msubst_LetNonRec in H_let_terminates.

  (* Find that we have terminating bindings *)
  inversion H_let_terminates. subst bs0 t0 v j0.
  clear H_let_terminates.
  rename H3 into H_b_bs_terminate.

  (* Push substitutions through, so we can find that
      γρ₁(let bs = ... in t) ⇓ e_f
  *)
  rewrite msubstA_bs_cons, msubst_bs_cons in H_b_bs_terminate.
  rewrite msubstA_TermBind, msubst_TermBind in H_b_bs_terminate.


  (* Two cases apply: E_Let and E_Error, E_Error_Let_TermBind *)
  inversion H_b_bs_terminate. subst x0 T t1 bs0 t0 v2.

  (* case E_Error_Let_TermBind *)
  2: {
    (** Contradiction: tb ⇓ Error, but tb is a safe binding, so
        it should terminate with a value *)
    unfold pure_open in *.
    assert (normal_Ty Tbn). {eauto using normalise_to_normal. }
    specialize (H_pure ltac:(assumption) ltac:(assumption) (msyn1 ρ) γ).

    assert (H_pure_γ : pure_substitution γ). { apply RG_pure_substitution_1 in H_Γ_γ_γ'. assumption. }
    assert (H_substitution_γ : substitution Γ γ). { apply RG_substitution_1 in H_Γ_γ_γ'. assumption. }

    assert (H_pure_closed : pure (close (msyn1 ρ) γ tb)) by auto.
    destruct H_pure_closed as [l [v [H_eval H_not_err]]].
    apply eval__deterministic in H_eval.
    unfold P_eval in H_eval.
    apply H_eval in H6 as [H_v_Error _].
    subst v.
    assert (is_error (Error T')) by constructor.
    contradiction.
    }

  rename H8 into H_bs_terminate.

  simpl in H_bs_terminate.

  (* To reduce in H_bs_terminate we need to consider the case:*)
  destruct
    (* binder x should not occur as let-bound variable in bs *)
    (existsb (eqb x) (bvbs <{ /[ γ /][bnr] (/[[ msyn1 ρ /][bnr] bs) }>)) eqn:H_ex.

    +
    (* TODO: I think this can be proven without H_unique (not a contradiction) *)

    (* 1. bvbs don't change with substitution *)
      rewrite bvbs_msubst_bnr in H_ex.
      rewrite bvbs_msubstA_bnr in H_ex.

      (* 2. existsb (eqb x) (bvbs bs) -> Term.appears_bound_in x (Let r bs t) *)

      apply existsb_appears_bound_in with (r := NonRec) (t := t) in H_ex.
      (* 3. Inversion on H_unique gives case: UNI_Let_TermBind *)

      inversion H_unique.
      (* 4. Contradiction with premise of that rule *)
      contradiction.

    +
      (* combine single substitution with multi-substitution *)
      rewrite compose_subst_msubst
            , compose_subst_msubst_bindings_nonrec in H_bs_terminate.

      (** Note about step indices
          k  : the overall budget for let b::bs in t
          j  : eval steps for let b::bs in t
          j1 : eval steps for b
          j2 : eval steps for let bs in t

          j < k
          j = j1 + 1 + j2
      *)

      (** Use fundamental property to find relates values for the
          RHS term tb. *)
      assert (H_LR_tb : LR_logically_approximate Δ Γ tb tb Tbn).
        { auto using LR_reflexivity. }
      destruct H_LR_tb as [_ [_ H_approx]].
      assert
         (H_RC_tb : RC k Tbn ρ
           <{ /[ γ  /] (/[[ msyn1 ρ /] tb) }>
           <{ /[ γ' /] (/[[ msyn2 ρ /] tb) }>).
           { eapply H_approx with (γ := γ) (γ' := γ'); auto. }
      clear H_approx.
      rewrite RV_RC in H_RC_tb.
      specialize (H_RC_tb j1 ltac:(lia) _ H6).
      destruct H_RC_tb as [v' [_ [_ H_RV_v1_v']]].

      remember ((x, v1) :: γ) as γₓ.
      remember ((x, v') :: γ') as γ'ₓ.
      apply E_Let in H_bs_terminate. (* use eval instead of eval_bindings_nonrec *)

      (** Construct related environments *)
      assert (H_γₓ_γ'ₓ : RG ρ (k - j1) ((x, Tbn) :: Γ) γₓ γ'ₓ).
      { subst γₓ γ'ₓ.
        eapply RG_cons.
        - eapply RV_monotone.
          + apply H_Δ_ρ.
          + apply H_RV_v1_v'.
          + lia.
        - eapply normalise_to_normal; eauto.
        - assumption.
        - eapply RG_monotone.
          + apply H_Δ_ρ.
          + apply H_Γ_γ_γ'.
          + lia.
      }

      (* Instantiate IH with γₓ and γ'ₓ for (k - j1) steps *)
      specialize (H_RC (k - j1) ρ γₓ γ'ₓ ).
      assert ( H_RC_ :
           RC (k - j1) Tn ρ
             <{ /[ γₓ /] (/[[ msyn1 ρ /] {Let NonRec bs t}) }>
             <{ /[ γ'ₓ /] (/[[ msyn2 ρ /] t') }>).
        { apply H_RC.
          - rewrite H_Δb. apply H_Δ_ρ.
          - rewrite H_Γb . apply H_γₓ_γ'ₓ.
        }

      (* push substitutions through, so we can use H_bs_terminate
         to conclude that γ'ₓρ₂(t') ⇓ e'_f *)
      rewrite msubstA_LetNonRec, msubst_LetNonRec in H_RC_.
      rewrite RV_RC in H_RC_.
      specialize (H_RC_ j2 (ltac: (lia)) _ H_bs_terminate).
      rename H_RC_ into H_t'_terminates.

      destruct H_t'_terminates as [e'_f [j' [H_t'_terminates RV_e_f_e'_f]]].
      eexists.
      eexists.
      split.

      * simpl in H_disjoint_b.
        unfold disjoint in H_disjoint_b.
        apply Forall_inv in H_disjoint_b.
        rewrite Heqγ'ₓ in H_t'_terminates.
        rewrite msubst_not_in_fv in H_t'_terminates.

        apply H_t'_terminates.
        rewrite fv_msubstA_fv.
        assumption.
      * eapply RV_monotone.
        -- eassumption.
        -- eassumption.
        -- lia.
Qed.


End CompatibilityLemmas.
