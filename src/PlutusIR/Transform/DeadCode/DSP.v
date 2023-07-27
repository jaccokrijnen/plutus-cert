From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.
From PlutusCert Require Import
  PlutusIR
  SemanticEquivalence.LogicalRelation
  Semantics.Static

  Transform.DeadCode
  Analysis.FreeVars
  Analysis.WellScoped
  Analysis.Purity
  Analysis.UniqueBinders

  Substitution
  AnnotationSubstitution
  Dynamic
  Static
  TypeSafety.TypeLanguage.Preservation
  Multisubstitution.Congruence

  Util.Tactics

  SemanticEquivalence.LogicalRelation
  SemanticEquivalence.Auto
  SemanticEquivalence.FundamentalProperty
  LetNonRec.DSP
.

Import NamedTerm.
Import ListNotations.
Import UniqueBinders.Term.

Set Diffs "on".

Definition disjoint {A} (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.


Definition subset {A} (xs ys : list A) := forall x, In x xs -> In x ys.
Notation "xs ⊆  ys" := (subset xs ys) (at level 0).

(* Uniqueness of binders for open terms *)
Definition unique_open Δ Γ t :=
  unique t /\
  Forall (fun X => ~ Annotation.appears_bound_in X t) Δ /\
  Forall (fun v => ~ Term.appears_bound_in v t) Γ.


Section SubstitutionLemmas.

Lemma subst_not_in_fv x t' t : ~ (In x (fv t)) -> <{ [t' / x] t }> = t.
Admitted.

(* Substituting type annotations will not change free term variables*)
Lemma fv_msubstA_fv γ t : fv <{ /[[ γ /] t }> = fv t.
Admitted.

Lemma msubst_not_in_fv x t' γ t : ~ (In x (fv t)) -> <{ /[(x, t') :: γ /] t }> = <{ /[γ/] t }>.
Admitted.

Lemma msubstA_LetNonRec ss bs t : <{ /[[ ss /] {Let NonRec bs t} }>
  = Let NonRec <{ /[[ ss /][bnr] bs }> <{/[[ ss /] t}>.
Admitted.

Lemma msubst_LetNonRec ss bs t : <{ /[ ss /] {Let NonRec bs t} }>
  = Let NonRec <{ /[ ss /][bnr] bs }> <{/[ ss /] t}>.
Admitted.

Lemma msubst_bs_cons ss b bs : <{ /[ ss /][bnr] {b :: bs} }>
  = <{ /[ ss /][b]b }> :: <{ /[ ss /][bnr]bs }>.
Admitted.

Lemma msubstA_bs_cons ss b bs : <{ /[[ ss /][bnr] {b :: bs} }>
  = <{ /[[ ss /][b]b }> :: <{ /[[ ss /][bnr]bs }>.
Admitted.

Lemma msubst_TermBind ss s x t : msubst_binding ss (TermBind s x t)
  = TermBind s x (msubst_term ss t).
Admitted.

Lemma msubstA_TermBind ss s x t : msubstA_binding ss (TermBind s x t)
  = TermBind s x (msubstA_term ss t).
Admitted.

Lemma compose_subst_msubst : forall x tx γ t,
  substitute x tx (msubst_term γ t) = msubst_term ((x, tx) :: γ) t.
Admitted.

Lemma compose_subst_msubst_bindings_nonrec : forall x tx γ bs,
  <{ [ tx / x ][bnr] (/[ γ /][bnr] bs) }> = <{ /[ (x, tx) :: γ /][bnr] bs }>.
Admitted.

Lemma value_msubstA_value v δ :
  value v ->
  value <{/[[ δ /] v}>.
Proof.
(** Should hold: only substitutes in types *)
Admitted.


Lemma value_msubst_value v γ :
  value v ->
  value <{/[ γ /] v}>.
Proof.
(** Should hold: only substitute under lambdas etc *)
Admitted.


End SubstitutionLemmas.


Section ScopingLemmas.
Lemma dead_code_strengthen {Δ Δ' Γ Γ' t t'}:
  elim t t' ->
  well_scoped Δ  Γ  t ->
  well_scoped Δ' Γ' t' ->
  Γ' ⊆  Γ.
Admitted.

Lemma well_scoped_fv {Δ Γ t}:
  well_scoped Δ Γ t ->
  forall v, In v (fv t) ->
  In v Γ.
Admitted.

Lemma strengthen_Γ Δ Γ x t Tx T :
  ~ In x (fv t) ->
  Δ,, (x , Tx) :: Γ |-+ t : T ->
  Δ,, Γ |-+ t : T
.
Admitted.

End ScopingLemmas.


Definition close ρ γ t := msubst_term γ (msubstA_term ρ t).

Section Purity.

(* Semantically pure _closed_ term *)
Definition pure t := exists k v, t =[k]=> v /\ ~ is_error v.

(* Only substitutes pure (closed) terms *)
Definition pure_substitution (γ : env) := Forall (fun '(x, t) => pure t) γ.

Lemma RG_pure_substitution_1 : forall ρ k Γ γ γ',
  RG ρ k Γ γ γ' -> pure_substitution γ.
Proof.
  intros ρ k Γ γ γ' H_RG.
  dependent induction H_RG.
  - constructor.
  - constructor.
    destruct H.
    assert (v1 =[0]=> v1). { apply eval_value__value. assumption. }
    + repeat eexists.
      all: eassumption.
    + assumption.
Qed.

Inductive substitution : tass -> env -> Prop :=
  | S_nil : substitution [] []
  | S_cons : forall Γ γ x t T,
      substitution Γ γ ->
      normal_Ty T ->
      ([] ,, [] |-+ t : T) ->
      substitution ((x, T) :: Γ) ((x, t) :: γ).

Lemma RG_substitution_1 : forall ρ k Γ γ γ', RG ρ k Γ γ γ' -> substitution Γ γ.
(* Should hold: substitution contains less information *)
Admitted.

(* Semantically pure _open_ term *)
Definition pure_open Δ Γ t τ :=
  normal_Ty τ ->
  Δ ,, Γ |-+ t : τ ->
  forall ρ γ,
  substitution Γ γ ->
  pure_substitution γ ->
  pure (close ρ γ t).

End Purity.


(** For the case of removing a subset of bindings

    TODO: generalize return type to take into account all of
    its binders (datatypes have multiple)

      disjoint (bvb b) (fv ...) /\ disjoint (btvb b) (Annotation.fv ...)

    Annotation.fv doesn't exist yet it seems.
    Move TypeSubstitution.ftv to FreeVars module
*)
Lemma unique_well_scoped_disjoint Δ Γ rec bs t Δ' Γ' bs' t' :
  elim (Let rec bs t) (Let rec bs' t') ->
  unique_open Δ Γ (Let rec bs t) ->
  well_scoped Δ  Γ  (Let rec bs  t ) ->
  well_scoped Δ' Γ' (Let rec bs' t') ->
  forall b,
  In b bs ->
  name_removed b bs' ->
  ~ In (name_Binding b) (fv (Let rec bs' t')).
Proof.
  intros
    H_dc H_unique H_ws_pre H_ws_post
    b H_In_b_bs H_removed_b_bs.
  intro H_in_fv.
  destruct b as [ s [v ty_v] t_b | tvd ty | dtd ]; simpl in *.

  (* TermBind *)
  - assert (H_v_in_Γ' : In v Γ').
      { eapply (well_scoped_fv H_ws_post _ H_in_fv). }
    assert (H_v_not_in_Γ' : ~ In v Γ').
      {
        (** v is bound in bs and therefore not in Γ (uniqueness).
            Then, by dead_code_strengthen, it is not in Γ' either
        *)
        assert (H_v_not_in_Γ : ~ In v Γ).
        {
          intros H_v_in_Γ.
          assert (H_v_nbi : ~ Term.appears_bound_in v (Let rec bs t)).
          {
            destruct H_unique as [_ [_ H_unique_Γ]].
            rewrite Forall_forall in H_unique_Γ.
            specialize (H_unique_Γ v H_v_in_Γ).
            assumption.
          }

          assert (H_v_bi : Term.appears_bound_in v (Let rec bs t)).
          {
            clear - H_In_b_bs.

            (* TODO simplify with auto *)
            induction bs; simpl in H_In_b_bs.
              - contradiction.
              - destruct H_In_b_bs.
                + subst.
                  apply Term.ABI_Let_TermBind1.
                + apply Term.ABI_Let_Cons.
                  auto.
          }
          contradiction.
        }

        apply (dead_code_strengthen H_dc H_ws_pre H_ws_post) in H_v_in_Γ'.
        contradiction.
      }
    contradiction.

  (* TypeBind *)
  - destruct tvd as [v k].
    assert (H_v_in_Δ' : In v Δ').
      { admit. (* similar to TermBind case *)}
    assert (H_v_no_in_Δ' : ~In v Δ').
      { admit. (* similar to TermBind case *)}
    contradiction.

  (* DatatypeBind *)
  - destruct dtd as [ [v k] vs vmatch cs].
    admit.

Admitted.



Section CompatibilityLemmas.

Lemma compat_TermBind_typing Δ Γ b x Tb tb Tbn bs t Tn :
  b = TermBind Strict (VarDecl x Tb) tb ->
  normalise Tb Tbn ->
  (Δ ,, Γ |-+ tb : Tbn) ->
  (Δ ,, (x, Tbn) :: Γ |-+ (Let NonRec       bs  t) : Tn) ->
  (Δ ,,             Γ  |-+ (Let NonRec (b :: bs) t) : Tn).
Proof.
Admitted.



Lemma compat_nil Δ Γ T t t' :
  Δ |-* T : Kind_Base -> (* May not be necessary, see #7 *)
  LR_logically_approximate Δ Γ           t  t' T ->
  LR_logically_approximate Δ Γ (Let NonRec [] t) t' T.
Proof.
  apply compatibility_LetNonRec_Nil__desugar.
Qed.

Lemma compat_TermBind pm_Δ pm_Γ t t' Tn b bs x Tb tb Tbn :
  pm_Δ |-* Tb : Kind_Base ->
  normalise Tb Tbn ->
  (pm_Δ ,, pm_Γ |-+ tb : Tbn) ->

  disjoint (bvb b) (fv t') ->
  unique t ->
  (* pure_binding [] b -> *)
  (* TODO, generalize pure_binding to arbitrary Γ, because this limits b to strictly bound values.
  This is not a typing environment though: for each var in scope,
  is it letbound strict/nonstrict or lambdabound *)

  forall pm_Δbs pm_Γbs,
    b = TermBind Strict (VarDecl x Tb) tb ->
    pure_open pm_Δ pm_Γ tb Tbn ->
    pm_Δbs = pm_Δ ->
    pm_Γbs = (x, Tbn) :: pm_Γ ->
    LR_logically_approximate pm_Δbs pm_Γbs (Let NonRec       bs  t) t' Tn ->
    LR_logically_approximate pm_Δ   pm_Γ   (Let NonRec (b :: bs) t) t' Tn.
Proof.
  intros H_Tb_kind H_Tbn H_tb_ty.
  intros H_disjoint_b H_unique.
  intros pm_Δbs pm_Γbs.
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
  inversion H_b_bs_terminate. subst s x0 T t1 bs0 t0 v2.

  (* case E_Error_Let_TermBind *)
  2: {
    (** Contradiction: tb ⇓ Error, but tb is a safe binding, so
        it should terminate with a value *)
    unfold pure_open in *.
    assert (normal_Ty Tbn). {eauto using normalise_to_normal. }
    specialize (H_pure ltac:(assumption) ltac:(assumption) (msyn1 ρ) γ).

    assert (H_pure_γ : pure_substitution γ). { apply RG_pure_substitution_1 in H_Γ_γ_γ'. assumption. }
    assert (H_substitution_γ : substitution pm_Γ γ). { apply RG_substitution_1 in H_Γ_γ_γ'. assumption. }

    assert (H_pure_closed : pure (close (msyn1 ρ) γ tb)) by auto.
    destruct H_pure_closed as [l [v [H_eval H_not_err]]].
    apply eval__deterministic in H_eval.
    unfold P_eval in H_eval.
    apply H_eval in H7 as [H_v_Error _].
    subst v.
    assert (is_error (Error T')) by constructor.
    contradiction.
    }

  rename H9 into H_bs_terminate.

  simpl in H_bs_terminate.
  destruct
    (* binder x should not occur as let-bound variable in bs *)
    (existsb (eqb x) (bvbs <{ /[ γ /][bnr] (/[[ msyn1 ρ /][bnr] bs) }>)).
    + admit. (* should be impossible by uniqueness *)
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
      assert (H_LR_tb : LR_logically_approximate pm_Δ pm_Γ tb tb Tbn).
        { auto using LR_reflexivity. }
      destruct H_LR_tb as [_ [_ H_approx]].
      assert
         (H_RC_tb : RC k Tbn ρ 
           <{ /[ γ  /] (/[[ msyn1 ρ /] tb) }>
           <{ /[ γ' /] (/[[ msyn2 ρ /] tb) }>).
           { eapply H_approx with (env0 := γ) (env' := γ'); auto. }
      clear H_approx.
      rewrite RV_RC in H_RC_tb.
      specialize (H_RC_tb j1 ltac:(lia) _ H7).
      destruct H_RC_tb as [v' [_ [_ H_RV_v1_v']]].

      remember ((x, v1) :: γ) as γₓ.
      remember ((x, v') :: γ') as γ'ₓ.
      apply E_Let in H_bs_terminate. (* use eval instead of eval_bindings_nonrec *)

      (** Construct related environments *)
      assert (H_γₓ_γ'ₓ : RG ρ (k - j1) ((x, Tbn) :: pm_Γ) γₓ γ'ₓ).
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
Admitted.



    (*
    γ(ρ(Let (b::bs) t)) ⇓ e_f
    Let (γρb::γρbs) (γρt) ⇓ e_f
    [v/x](Let γρbs γρt) ⇓ e_f
    Let ([v/x]γρbs) ([v/x]γρt) ⇓ e_f
    by IH: [v/x]γt' ⇓ e_f'
    since x ∉ t': γt' ⇓ e_f'


    *)

Lemma compatibility_dc_delete_let Δ Γ t t' T Tn r bs Δ' Γ' bsn :
  Δ |-* T : Kind_Base ->
  normalise T Tn ->
  Δ ,, Γ |-+ (Let r bs t) : Tn ->

  unique (Let r bs t) ->
  disjoint (fv t') (bound_vars_bindings bs) ->
  Forall (pure_binding []) bs ->

  (* Extended environments *)
  Δ' = (ty_binds_bindings bs) ++ Δ  ->
  map_normalise (binds_bindings bs) bsn ->
  Γ' = bsn ++ Γ bsn ->


  LR_logically_approximate Δ' Γ'   t            t' Tn ->
  LR_logically_approximate Δ  Γ    (Let r bs t) t' Tn.
Proof with auto.
intros Tn_k T_Tn H_Let_Tn.
intros let_uniq bvs_not_in_t' bs_safe.
intros H_Δ' H_bsn H_Γ'.
intros H_approx_t_t'.

unfold LR_logically_approximate.
repeat split.
1,2: admit.


(* Different representations of envronments *)
rename
  Γ into _Γ,
  Γ' into _Γ',
  Δ into _Δ,
  Δ' into _Δ'.

intros k ρ γ γ' Γ Δ H_eq_Δ_ck H_eq_Γ_ck.

intros H_good_ρ H_γ_γ'.
autorewrite with RC.

unfold LR_logically_approximate in H_approx_t_t'.
destruct_hypos.
intros j H_j_k e_f H_Let_eval.


Admitted.

End CompatibilityLemmas.

(*
Theorem dead_code_Term_DSP : forall Δ Γ,



Definition P_has_type Δ Γ t T : Prop :=
  forall t',
    dead_code t t' ->
    LR_logically_approximate Δ Γ t t' T.

Definition P_constructor_well_formed Delta c Tr : Prop := Delta |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Delta Gamma bs : Prop := 
  True.

Definition P_bindings_well_formed_rec Delta Gamma bs1 : Prop := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b : Prop := 
  True.
*)



