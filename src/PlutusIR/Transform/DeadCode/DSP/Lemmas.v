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

Import PlutusNotations.

Import ListNotations.
Import UniqueBinders.Term.

Set Diffs "on".

(* TODO: rename the actual functions *)
Definition fv : Term -> list string := (Term.fv string_dec).
Definition fv_binding : Recursivity -> Binding -> list string := (Term.fvb string_dec).
Definition fv_bindings : Recursivity -> list Binding -> list string := (Term.fvbs string_dec fv_binding).

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

End Purity.

Lemma Forall_singleton {A} P (x : A) :
  Forall P [x] <-> P x.
Proof.
  split.
  - inversion 1. assumption.
  - auto.
Qed.


(** For the case of removing a subset of bindings

*)
(*
    TODO: generalize return type to take into account all of
    its binders (datatypes have multiple)

      disjoint (bvb b) (fv ...) /\ disjoint (btvb b) (Annotation.fv ...)

    Annotation.fv doesn't exist yet it seems.
    Move TypeSubstitution.ftv to FreeVars module
*)
Lemma unique_well_scoped_disjoint Δ Γ rec bs t Δ' Γ' bs' t' :
  elim (Let rec bs t) (Let rec bs' t') ->
  unique_open Δ  Γ  (Let rec bs  t ) ->
  well_scoped Δ  Γ  (Let rec bs  t ) ->
  well_scoped Δ' Γ' (Let rec bs' t') ->
  forall b,
  In b bs ->
  name_removed b bs' ->
  disjoint (bvb b) (fv (Let rec bs' t')).
  (* /\ disjoint (btvb b) (ftv (Let rec bs' t')).*)
Proof.
  intros
    H_dc H_unique H_ws_pre H_ws_post
    b H_In_b_bs H_removed_b_bs.
  destruct b as [ s [v ty_v] t_b | tvd ty | dtd ]; simpl in *.

  (* TermBind *)
  - unfold disjoint.
    apply Forall_singleton.
    intros H_in_fv.

    assert (H_v_in_Γ' : In v Γ').
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
