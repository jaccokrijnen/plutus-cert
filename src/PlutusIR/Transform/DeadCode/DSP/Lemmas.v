From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import Analysis.WellScoped.
From PlutusCert Require Import TypeSafety.TypeLanguage.Preservation.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import FreeVars.
From PlutusCert Require Import Purity.
From PlutusCert Require Import SubstitutionNonFree.

Import ListNotations.
Import UniqueBinders.
Import Utf8_core.


Definition disjoint {A} (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.


Definition subset {A} (xs ys : list A) := forall x, In x xs -> In x ys.
Notation "xs ⊆  ys" := (subset xs ys) (at level 11).

Notation "xs \ ys" := (remove_many string_dec ys xs) (at level 10).

(* Uniqueness of binders for open terms *)
Definition unique_open Δ Γ t :=
  unique_tm t /\
  Forall (fun X => ~ appears_bound_in_ann X t) Δ /\
  Forall (fun v => ~ appears_bound_in_tm v t) Γ.


Section TypingHelpers.

  Lemma strengthen_Γ Δ Γ x t Tx T :
    ~ In x (fv t) ->
    Δ,, (x , Tx) :: Γ |-+ t : T ->
    Δ,, Γ |-+ t : T
  .
  Admitted.

End TypingHelpers.

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

  (*
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
  *)

  (*
  Lemma msubst_TermBind ss s x t : msubst_b ss (TermBind s x t)
    = TermBind s x (msubst ss t).
  Admitted.

  Lemma msubstA_TermBind ss s x t : msubstA_b ss (TermBind s x t)
    = TermBind s x (msubstA ss t).
  Admitted.
  *)

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

  Lemma subset_remove_many xs ys zs :
    xs ⊆ (ys ++ zs) ->
    xs \ ys  ⊆ zs.
  Admitted.

  Lemma subset_rev_l A (xs ys zs : list A):
    xs ⊆ (rev ys ++ zs) ->
    xs ⊆ (ys ++ zs).
  Admitted.

  Lemma subset_remove_many_l xs ys zs :
    xs ⊆ zs ->
    xs \ ys ⊆ zs.
  Admitted.

  Lemma remove_many_app_comm : ∀ xs ys zs, xs \ (ys ++ zs) = xs \ (zs ++ ys).
  Admitted.

  Lemma remove_many_app_r : ∀ xs ys zs, xs \ (ys ++ zs) = (xs \ ys) \ zs.
  Admitted.

  Lemma remove_many_app : ∀ xs ys zs, (ys ++ zs) \ xs = ys \ xs ++ zs \ xs.
  Admitted.

  Lemma remove_many_empty : ∀ xs,
    [] \ xs = [].
  Admitted.


End SubsetHelpers.

Section ScopingLemmas.

  Lemma well_scoped_bindings_Rec__Forall Δ Γ bs :
    Δ,, Γ |-ws_oks_r bs ->
    Forall (fun b => Δ ,, Γ |-ws_ok_b b) bs.
  Proof.
    intros H_ws.
    dependent induction H_ws.
    all: auto using Forall.
  Qed.



  (* Specialized equation of fv_bindings in case of Let Rec *)
  Lemma fv_bindings_eq bs :
    fv_bindings Rec bs = (List.concat (map (fv_binding Rec) bs)) \ (bvbs bs).
  Proof.
    destruct bs.
    - reflexivity.
    - unfold fv_bindings. rewrite FreeVars.Term.fvbs_equation.
      reflexivity.
  Qed.

  Lemma fv_binding_Rec__fv_bindings_Rec bs Γ :
    Forall (fun b => (fv_binding Rec b) \ (bvbs bs) ⊆ Γ) bs ->
    fv_bindings Rec bs ⊆ Γ.
  Proof.
    intros H_bs.
    unfold fv_bindings.
    rewrite fv_bindings_eq.
    revert H_bs.
    (* Generalize (bvbs bs) so it stays constant in the IH *)
    generalize (bvbs bs).
    intros vars H_bs.
    induction bs; simpl.
    - rewrite remove_many_empty.
      apply empty_subset.
    - inversion H_bs. subst.
      rewrite remove_many_app.
      apply subset_append.
      + assumption.
      + auto.
  Qed.

  (* Use fv_equation to unfold fv one step *)
  Ltac simpl_fv :=
      unfold fv; rewrite Term.fv_equation
    .

  Ltac simpl_fvb :=
      unfold fv_binding; rewrite Term.fvb_equation
    .

  Ltac use_IH :=
      intros;
      simpl_fv;
      inversion H_ws; subst;
     eauto.

  Definition P_Term (t : Term) : Prop :=
    ∀ Δ Γ (H_ws : well_scoped Δ Γ t),
    fv t ⊆ Γ.

  Definition P_Binding (b : Binding) :=
    ∀ Δ Γ rec (H_ws_bs : binding_well_formed Δ Γ b),
    fv_binding rec b ⊆ Γ.

  (* The free variables of a well-scoped term appear in Γ *)
  Lemma well_scoped_fv : (∀ t, P_Term t) /\ (∀ b, P_Binding b).
  Proof.
    apply Term__multind with (P := P_Term) (Q := P_Binding).
    all: simpl; unfold P_Term; unfold P_Binding.
    - (* Let *)
      intros rec bs t IH_bs IH_t Δ Γ H_ws.
      simpl_fv.
      fold fv_binding fv_bindings fv.
      inversion H_ws; subst.
      + (* NonRec *)
        apply subset_append.
        * (* Free vars of bs are in Γ *)
          clear - IH_bs H4.
          revert Δ Γ IH_bs H4.
          induction bs as [ | b bs]; intros.
          **  simpl. unfold subset.
              intros.
              inversion H.
          ** inversion IH_bs; subst.
             inversion H4; subst.
             assert
               (HH : fv_bindings NonRec bs ⊆ (bvb b ++ Γ)) by eauto.
             unfold fv_bindings.
             rewrite Term.fvbs_equation.
             fold fv_bindings.
             apply subset_append.
             *** inversion IH_bs; subst.
                 eapply H6. eauto.
             *** apply subset_remove_many. eauto.
       * (* Free vars in (t \ bvbs) are in Γ*)
         assert (fv t ⊆ (rev (bvbs bs) ++ Γ)) by eauto.
         apply subset_rev_l in H.
         eauto using subset_remove_many.

      + (* Rec *)
        apply subset_append.
        * apply fv_binding_Rec__fv_bindings_Rec.
          apply well_scoped_bindings_Rec__Forall in H4.

          rewrite Util.ForallP_Forall in IH_bs.
          rewrite Forall_forall in *.
          intros b H_b_bs.

          specialize (H4 b H_b_bs).
          eapply IH_bs with (rec := Rec) in H4.
          ** apply subset_rev_l in H4.
             apply subset_remove_many.
             assumption.
          ** assumption.
        * apply IH_t in H5.
          apply subset_rev_l in H5.
          apply subset_remove_many.
          assumption.

    - (* Var *)
      intros x Δ Γ H_ws.
      unfold fv; rewrite Term.fv_equation.
      inversion H_ws. subst.
      unfold subset.
      intros x' H_in.
      assert (x' = x) by eauto using in_singleton_eq.
      subst.
      auto.

    - (* TyAbs *)
      use_IH.

    - (* LamAbs *)
      intros x τ t IH_t Δ Γ.
      intro.
      simpl_fv.
      inversion H_ws; subst.
      specialize (IH_t _ _ H3).

      remember (remove string_dec x (Term.fv string_dec t)) as fv'.

      assert (x ∉ fv'). {
        subst fv'.
        eapply remove_In.
      }

      eapply (subset_cons (x := x)).
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

    - (* TermBind *)
      intros s [x ty] t IH_t Δ Γ rec H_ws_b.
      destruct rec.
      all: simpl_fvb.
      + (* NonRec*)
        inversion H_ws_b; subst.
        eauto.
      + inversion H_ws_b; subst.
        eapply remove_subset.
        eauto.
    - (* TypeBind *)
      + intros.
        simpl_fvb.
        apply empty_subset.
    - intros dtd Δ Γ rec H_ws.
      simpl_fvb.
      apply empty_subset.

  Qed.

  Corollary well_scoped_fv_term t Δ Γ :
    (Δ,, Γ |-+ t) -> 
    fv t ⊆ Γ.
    revert Δ Γ.
    apply (proj1 well_scoped_fv t).
  Qed.

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

Lemma close_equation : ∀ ρ γ t,
  close ρ γ t = msubst γ (msubstA ρ t).
Proof. reflexivity. Qed.

Definition close_bnr ρ γ bs := msubst_bnr γ (msubstA_bnr ρ bs).

Lemma close_bnr_equation : ∀ ρ γ bs,
  close_bnr ρ γ bs = msubst_bnr γ (msubstA_bnr ρ bs).
Proof. reflexivity. Qed.

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

  Definition pure_binding Δ Γ b :=
    match b with
      | TermBind Strict (VarDecl _ T) t => exists Tn, normalise T Tn /\ pure_open Δ Γ t Tn
      | _ => True
    end.


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

Lemma disjoint_contradiction {A} {xs ys} {x : A} :
  x ∈ xs ->
  x ∈ ys ->
  ¬ (disjoint xs ys).
Admitted.

Lemma unique_well_scoped_disjoint Δ Γ rec bs t Δ' Γ' t' :

  (* Properties on pre-term *)
  well_scoped Δ Γ (Let rec bs t) ->
  unique_open Δ Γ (Let rec bs t) ->

  (* Properties on post-term *)
  well_scoped Δ' Γ' t' ->

  Δ' ⊆ Δ ->
  Γ' ⊆ Γ ->
  forall b,
    In b bs ->
    disjoint (bvb b) (fv t') /\
    disjoint (btvb b) (ftv t').
Proof with eauto.
  intros H_pre_ws H_pre_unique H_post_ws H_Δ_Δ' H_Γ_Γ'.
  intros b H_in_b_bs .

  destruct b as [ s [x ty] t_rhs | | ].
  all: split.

  (* TermBind term variables *)
  - unfold disjoint.

    (* TermBind *)
    + simpl.
      rewrite Forall_singleton.
      intros H_x_in_fv.

      assert (H_x_in_Γ : x ∈ Γ). {
        apply H_Γ_Γ'.
        eapply well_scoped_fv_term...
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
