From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import Transform.DeadCode.
From PlutusCert Require Import Analysis.WellScoped.
From PlutusCert Require Import TypeSafety.TypeLanguage.Preservation.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import FreeVars.
From PlutusCert Require Import Purity.
From PlutusCert Require Import SubstitutionNonFree.

Import ListNotations.
Import UniqueBinders.Term.
Import Utf8_core.

Set Diffs "on".


Definition disjoint {A} (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.


Definition subset {A} (xs ys : list A) := forall x, In x xs -> In x ys.
Notation "xs ⊆  ys" := (subset xs ys) (at level 11).

(* Uniqueness of binders for open terms *)
Definition unique_open Δ Γ t :=
  unique t /\
  Forall (fun X => ~ Annotation.appears_bound_in X t) Δ /\
  Forall (fun v => ~ Term.appears_bound_in v t) Γ.



Section SubstitutionLemmas.


  Lemma msubst_not_in_fv x t' γ t :
    x ∉ fv t ->
    msubst ((x, t') :: γ) t = msubst γ t.
  Proof.
  Admitted.

  (* Substituting type annotations will not change free term variables*)
  Lemma fv_msubstA_fv ρ t :
    fv (msubstA ρ t) = fv t.
  Admitted.


  Import PlutusNotations.

  Lemma msubstA_LetNonRec ss bs t :
    <{ /[[ ss /] {Let NonRec bs t} }>
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

  Lemma msubst_TermBind ss s x t : msubst_b ss (TermBind s x t)
    = TermBind s x (msubst ss t).
  Admitted.

  Lemma msubstA_TermBind ss s x t : msubstA_b ss (TermBind s x t)
    = TermBind s x (msubstA ss t).
  Admitted.

  Lemma compose_subst_msubst : forall x tx γ t,
    subst x tx (msubst γ t) = msubst ((x, tx) :: γ) t.
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

Section SubsetHelpers.

  Lemma subset_cons {A} {xs ys} {x : A}:
   xs ⊆ (x :: ys) ->
   x ∉ xs ->
   xs ⊆ ys.
  Admitted.

  Lemma remove_subset {xs ys} {x : string}:
   xs ⊆ ys ->
   (remove string_dec x xs) ⊆ ys.
  Admitted.

  Lemma subset_append {A} {xs ys zs : list A} :
    xs ⊆ zs -> 
    ys ⊆ zs ->
    (xs ++ ys) ⊆ zs.
  Admitted.

  Lemma empty_subset {A} {xs : list A} :
    [] ⊆ xs.
  Admitted.

  Lemma in_singleton_eq {A} {x y : A} :
    x ∈ [y] ->
    x = y.
  Admitted.

End SubsetHelpers.

Section ScopingLemmas.

  Lemma well_scoped_weaken {Δ Γ Δ' Γ' t} :
    Δ ⊆ Δ' ->
    Γ ⊆ Γ' ->
    well_scoped Δ' Γ' t ->
    well_scoped Δ Γ t.
  Admitted.


  (* Use fv_equation to unfold fv one step *)
  Ltac simpl_fv :=
      unfold fv; rewrite Term.fv_equation
    .

  Ltac use_IH :=
      simpl_fv;
      inversion H_ws; subst;
     eauto.


  (* The free variables of a well-scoped term appear in Γ *)
  Lemma well_scoped_fv {Δ Γ t}:
    well_scoped Δ Γ t ->
    fv t ⊆ Γ.
  Proof.
    revert Δ Γ.
    induction t; simpl; intros Δ Γ H_ws.
    - (* Let *)
      simpl_fv.
      inversion H_ws; subst.
      + (* NonRec *)
        (* TODO: prove using mutual induction on bindings *)
        admit.
      + (* Rec *)
        (* TODO: prove using mutual induction on bindings *)
        admit.

    - (* Var *)
      unfold fv; rewrite Term.fv_equation.
      inversion H_ws. subst.
      unfold subset.
      intros.
      assert (x = n) by eauto using in_singleton_eq.
      subst.
      auto.

    - (* TyAbs *)
      use_IH.

    - (* LamAbs *)
      simpl_fv.
      inversion H_ws; subst.
      specialize (IHt _ _ H3).

      remember (remove string_dec b (Term.fv string_dec t0)) as fv'.

      assert (b ∉ fv'). {
        subst fv'.
        eapply remove_In.
      }

      eapply (subset_cons (x := b)).
      + subst fv'. auto using remove_subset.
      + assumption.

    -  (* Apply *)
      use_IH.
      apply subset_append; eauto.

    - (* Constant*)
      use_IH.
      apply empty_subset.

    - (* Builtin *)
      use_IH.
      apply empty_subset.

    - (* TyInst *)
      use_IH.

    - (* Error *)
      use_IH.
      apply empty_subset.

    - (* IWrap *)
      use_IH.

    - (* Unwrap *)
      use_IH.

  Admitted.


  (* The free type variables of a well-scoped term appear in Γ *)
  Lemma well_scoped_ftv {Δ Γ t}:
    well_scoped Δ Γ t ->
    ftv t ⊆ Δ.
  Admitted.

  Lemma well_scoped_unique { Δ Γ t } :
    well_scoped Δ Γ t ->
    unique_open Δ Γ t ->
    disjoint Γ (bound_vars t).
  Proof.

  (* Follows from unique_open:
      Forall (λ v : string, ¬ Term.appears_bound_in v t) Γ
  *)
  Admitted.


End ScopingLemmas.


Definition close ρ γ t := msubst γ (msubstA ρ t).

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


  Lemma msubst_value t γ ρ:
    value t /\ ~ is_error t ->
    value (msubst γ (msubstA ρ t)) /\ ~ is_error (msubst γ (msubstA ρ t)).
  Admitted.

  Lemma is_pure_nil_pure_open Δ Γ t τ:
    is_pure [] t ->
    pure_open Δ Γ t τ.
  Proof.
    intros H_is_pure H_normal H_ty ρ γ Γ_γ γ_pure.
    inversion H_is_pure.
    - unfold pure, close.
      remember (msubst γ (msubstA ρ t)) as t'.
      assert (H_t' : value t' /\ ~ is_error t').
      { subst. auto using msubst_value. }
      destruct H_t'.
      exists 0, t'.
      split.
      + apply eval_value. assumption.
      + assumption.
    - inversion H.
    - inversion H.
  Qed.


End Purity.

Lemma Forall_singleton {A} P (x : A) :
  Forall P [x] <-> P x.
Proof.
  split.
  - inversion 1. assumption.
  - auto.
Qed.

Definition pre Δ Γ t :=
  well_scoped Δ Γ t /\
  unique_open Δ Γ t.

Definition post Δ Γ t :=
  well_scoped Δ Γ t.


Lemma disjoint_contradiction {A} {xs ys} {x : A} :
  x ∈ xs ->
  x ∈ ys ->
  ¬ (disjoint xs ys).
Admitted.



Ltac use_IH :=
    inversion H_elim; subst;
    inversion X; subst;
    inversion H_ws_post; subst;
    inversion H_ws_pre; subst;
    try constructor;
    eauto.

(* The post term is well-scoped in the kind/type environment
   of the pre-term *)
Lemma elim_well_scoped {Δ Γ Δ' Γ' t t'} :
  elim t t' ->
  well_scoped Δ Γ t ->
  well_scoped Δ' Γ' t' ->
  Δ' ⊆ Δ -> (* invariant *)
  Γ' ⊆ Γ -> (* invariant *)
  well_scoped Δ Γ t'.
Proof.
  revert Δ Γ Δ' Γ' t'.
  induction t.
  all: intros Δ Γ Δ' Γ' t' H_elim H_ws_pre H_ws_post H_sub_env.

  (* All cases except for Let *)
  all: try use_IH.

  - (* Let *)
    inversion H_elim; subst.

    (* elim_compat *)
    + admit.

    (* elim_delete_let*)
    + admit.

    (* elim_delete_bindings *)
    + admit.

Admitted.

Lemma unique_well_scoped_disjoint Δ Γ rec bs t Δ' Γ' bs' t' :
  elim t t' ->
  elim_bindings bs bs' ->

  (* Properties on pre- and post-term*)
  pre Δ Γ (Let rec bs t) ->
  post Δ' Γ' (Let rec bs' t') ->

  Δ' ⊆ Δ ->
  Γ' ⊆ Γ ->
  forall b,
    In b bs ->
    name b ∉ map name bs' ->
    disjoint (bvb b) (fv (Let rec bs' t')) /\
    disjoint (btvb b) (ftv (Let rec bs' t')).
Proof with eauto.
  intros H_elim H_elim_bs [H_pre_ws H_pre_unique] H_post_ws H_Δ_Δ' H_Γ_Γ'.
  intros b H_in_b_bs H_name_gone.

  (* The post-term is also well-scoped under Δ; Γ *)
  assert (H_post_ws_Δ_Γ : well_scoped Δ Γ (Let rec bs' t')). {
    eapply elim_well_scoped.
    all: eauto.
    apply elim_delete_bindings.
    all: eauto.
  }

  destruct b as [ s [x ty] t_rhs | | ].
  all: split.

  (* TermBind term variables *)
  - unfold disjoint.

    (* TermBind *)
    + simpl.
      rewrite Forall_singleton.
      intros H_x_in_fv.

      assert (H_x_in_Γ : x ∈ Γ). {
        eapply (well_scoped_fv H_post_ws_Δ_Γ)...
      }

      assert (H_x_in_bound_vars : x ∈ bound_vars (Let rec bs t)). {
        admit.
        (* TermBind s (VarDecl x ty) t_rhs ∈ bs *)
      }

      assert (H_disjoint := well_scoped_unique H_pre_ws H_pre_unique).
      assert (H_not_disjoint : ¬ (disjoint Γ (bound_vars (Let rec bs t)))). {
        eapply (disjoint_contradiction H_x_in_Γ H_x_in_bound_vars).
      }
      contradiction.

  - (* TermBind type-variables*)
    admit.

  - (* TypeBind term-variables *)
    admit.

  - (* TypeBind type-variables *)
    admit.

  - (* DatatypeBind term-variables *)
    admit.

  - (* DatatypeBind type-variables *)
    admit.
Admitted.
