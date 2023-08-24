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


Section Term.
  Import FreeVars.Term.

  Definition fv : Term -> list string := (Term.fv string_dec).
  Definition ftv : Term -> list string := (Term.ftv string_dec).
  Definition fv_binding : Recursivity -> Binding -> list string := (Term.fvb string_dec).
  Definition fv_bindings : Recursivity -> list Binding -> list string := (Term.fvbs string_dec fv_binding).


  Lemma not_in_app : ∀ A (x : A) xs xs',
    x ∉ (xs ++ xs') ->
    x ∉ xs /\ x ∉ xs'.
  Proof.
    intros A x xs xs' H_notin.
    induction xs as [ | x' xs].
    all: split; auto.
    - cbn - [In] in H_notin.
      apply not_in_cons in H_notin as [H_x_x' H_xs_xs'].
      apply IHxs in H_xs_xs' as [ ].
      apply not_in_cons.
      auto.
    - eapply proj2.
      apply IHxs.
      cbn - [In] in H_notin.
      apply not_in_cons in H_notin.
      destruct H_notin; eauto.
  Qed.

  Lemma not_in_fv_TyAbs x v k t :
    x ∉ fv (TyAbs k v t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_LamAbs x y ty t :
    x ∉ fv (LamAbs y ty t) ->
    (x =? y)%string = false -> (* TODO, require x ≠ y, either in bool or prop form *)
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Apply_l x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Apply_r x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t'.
  Admitted.


  Lemma not_in_fv_Constant x c :
    x ∉ fv (Constant c).
  Admitted.

  Lemma not_in_fv_Builtin x f :
    x ∉ fv (Builtin f).
  Admitted.

  Lemma not_in_fv_TyInst x t ty :
    x ∉ fv (TyInst t ty) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Error x ty :
    x ∉ fv (Error ty).
  Admitted.

  Lemma not_in_fv_IWrap x ty1 ty2 t:
    x ∉ fv (IWrap ty1 ty2 t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Unwrap x t :
    x ∉ fv (Unwrap t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_TermBind x r s y ty t:
    x ∉ fv_binding r (TermBind s (VarDecl y ty) t) ->
    False ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Let_NonRec_t x r bs t :
    x ∉ fv (Let r bs t) ->
    existsb (eqb x) (bvbs bs) = false ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Let_NonRec_b x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    x ∉ fv_binding NonRec b.
  Admitted.

  Lemma not_in_fv_Let_NonRec_bs x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    existsb (eqb x) (bvb b) = false ->
    x ∉ fv (Let NonRec bs t).
  Admitted.

  Create HintDb not_in.
  Hint Resolve
    not_in_fv_TyAbs 
    not_in_fv_LamAbs
    not_in_fv_Apply_l
    not_in_fv_Apply_r
    not_in_fv_Constant
    not_in_fv_Builtin
    not_in_fv_TyInst
    not_in_fv_Error
    not_in_fv_IWrap
    not_in_fv_Unwrap
    : not_in.

  Lemma fv_let_cons x b bs t :
    (x ∈ fv (Let NonRec bs t)) ->
    (x ∈ fv (Let NonRec (b :: bs) t)).
  Admitted.

  Definition P_Term t := forall x t',
    x ∉ fv t ->
    subst x t' t = t.

  Definition P_Binding b := forall r x t',
    x ∉ fv_binding r b ->
    subst_b x t' b = b.

  Lemma existsb_bvbs_bs x (b : Binding) bs :
    existsb (eqb x) (bvbs (b :: bs)) = true ->
    existsb (eqb x) (bvb b) = false ->
    existsb (eqb x) (bvbs bs) = true.
  Proof.
    intros H_in_bvbs H_not_in_bvb.
              unfold bvbs in H_in_bvbs.
              simpl in H_in_bvbs.
              rewrite existsb_app in H_in_bvbs.
              rewrite Bool.orb_true_iff in H_in_bvbs.
              destruct H_in_bvbs.
              **
                 rewrite H in H_not_in_bvb.
                 inversion H_not_in_bvb.
              ** eauto.
  Qed.

  Lemma existsb_In x xs :
    existsb (eqb x) xs = true ->
    x ∈ xs.
  Proof.
    intros H_ex.
    induction xs.
    - inversion H_ex.
    - destruct (string_dec x a); subst.
      + apply in_eq.
      + 
        apply existsb_exists in H_ex as [].
        destruct H.
        apply eqb_eq in H0; subst.
        assumption.
  Qed.

  Lemma existsb_not_in x xs :
    existsb (eqb x) xs = false ->
    x ∉ xs.
  Proof.
  Admitted.


  Lemma subst_br_not_in_fv x t' bs t :
    x ∉ fv (Let Rec bs t) ->
    Util.ForallP P_Binding bs ->
    existsb (eqb x) (bvbs bs) = false ->
    subst_br x t' bs = bs.
  Proof.
  Admitted.

  Lemma subst_bnr_not_in_fv x t' bs t:
    x ∉ fv (Let NonRec bs t) ->
    Forall P_Binding bs ->
    subst_bnr x t' bs = bs.
  Proof.
    intros H_not_in_fv H_bs.
    induction bs as [ | b bs].
    - reflexivity.
    - simpl.
      destruct (existsb (eqb x) (bvb b)) eqn:H_in_bvb.
      all: inversion H_bs; subst.
      + apply not_in_fv_Let_NonRec_b in H_not_in_fv.
        f_equal.
        eauto.
      + (* x must be bound in bs *)
        f_equal.
          * apply not_in_fv_Let_NonRec_b in H_not_in_fv.
            eauto.
          *
          destruct (existsb (eqb x) (bvbs bs)) eqn:H_ex_bvbs. 
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using not_in_fv_Let_NonRec_bs.
               eauto using existsb_bvbs_bs.
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using  not_in_fv_Let_NonRec_bs.
               assert (x ∉ bvbs bs). {
                 apply existsb_not_in in H_ex_bvbs.
                 assumption.
               }
               eauto.
  Qed.


  Lemma subst_not_in_fv : forall t, P_Term t.
  Proof.
    apply Term__multind with (P := P_Term) (Q := P_Binding).

    all: try (
      unfold P_Term in *;
      intros;
      rewrite subst_equation;
      f_equal;
      eauto with not_in
   ).

    (* Let *)
    - destruct rec; destruct (existsb (eqb x) (bvbs bs)) eqn:H_existsb.

      (* Let NonRec *)
      + (* x does not occur free, but is shadowed in bs *)
        f_equal.
        rewrite subst_bnr'_equation.
        induction bs.
        * reflexivity.
        * destruct (existsb (eqb x) (bvb a)) eqn:H_exists_here.
          ** inversion H. subst. unfold P_Binding in H4.
             apply not_in_fv_Let_NonRec_b in H1.
             f_equal.
             f_equal.
             eauto.
          ** f_equal.
              ***
                  apply not_in_fv_Let_NonRec_b in H1.
                  inversion H. subst. unfold P_Binding in H4.
                  eauto.
              *** inversion H; subst. rewrite Util.ForallP_Forall in H5.
                  eauto using subst_bnr_not_in_fv, existsb_bvbs_bs, not_in_fv_Let_NonRec_bs.

      (* Let NonRec *)
      + (* x does not occur free and is also not bound in bs *)
        f_equal.
        rewrite Util.ForallP_Forall in H.
        * eapply subst_bnr_not_in_fv with (t := t); eauto.
        * assert (x ∉ fv t). {
            apply not_in_fv_Let_NonRec_t in H1; eauto.
            }
          eauto.
      + reflexivity.
      + f_equal.
        * eapply subst_br_not_in_fv with (t := t); eauto.
        * eapply not_in_fv_Let_NonRec_t in H1; eauto.

    (* Var *)
    - simpl in H.
      destruct (x =? s)%string eqn:H_eqb.
      + apply eqb_eq in H_eqb.
        apply eq_sym in H_eqb.
        assert False. auto.
        contradiction.
      + reflexivity.

    (* LamAbs *)
    -
      destruct (x =? s)%string eqn:H_eqb.
      + reflexivity.
      + f_equal; eauto with not_in.

    (* TermBind *)
    - unfold P_Term, P_Binding.
      intros.
      rewrite subst_b_equation.
      destruct v as [y ty].
      destruct (x =? y)%string eqn:H_eqb.
      + unfold fv_binding in *.
        destruct r.
        rewrite fvb_equation in H0.
        *
          f_equal.
          eauto.
        * f_equal.
          rewrite eqb_eq in H_eqb. subst.
      f_equal.
      unfold fv_binding in H0.
      rewrite fvb_equation in H0.
      admit.
      + admit.

    (* TypeBind *)
    - unfold P_Binding.
      reflexivity.

    (* DatatypeBind *)
    - unfold P_Binding.
      reflexivity.
Admitted.



End Term.

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


Section ScopingLemmas.

  Lemma dead_code_strengthen {Δ Δ' Γ Γ' t t'}:
    elim t t' ->
    well_scoped Δ  Γ  t ->
    well_scoped Δ' Γ' t' ->
    Γ' ⊆ Γ.
  Admitted.
  (* Is this true? *)

  Lemma strengthen_Γ Δ Γ x t Tx T :
    ~ In x (fv t) ->
    Δ,, (x , Tx) :: Γ |-+ t : T ->
    Δ,, Γ |-+ t : T
  .
  Admitted.

  Lemma elim_ws {Δ Γ t t'}:
    elim t t' ->
    well_scoped Δ Γ t ->
    well_scoped Δ Γ t'.
  Admitted.

  Lemma elim_fv {t t'}:
    elim t t' ->
    fv t ⊆ fv t'.
  Admitted.

  Lemma elim_abi {t t' x} :
    elim t t' ->
    Term.appears_bound_in x t' ->
    Term.appears_bound_in x t.
  (* By conditions of elim_bindings_pure *)
  Admitted.

  Lemma elim_abi_annotation {t t' x} :
    elim t t' ->
    Annotation.appears_bound_in x t' ->
    Annotation.appears_bound_in x t.
  (* By conditions of elim_bindings_pure *)
  Admitted.

  Lemma elim_bvbs {bs bs'} :
    elim_bindings bs bs' ->
    bvbs bs' ⊆ bvbs bs.
  (* By conditions of elim_bindings_pure *)
  Admitted.

  Lemma well_scoped_fv_ftv {t} :
    well_scoped (ftv t) (fv t) t.
  Admitted.

  Lemma well_scoped_fv {Δ Γ t}:
    well_scoped Δ Γ t ->
    fv t ⊆ Γ.
  Admitted.

  Lemma well_scoped_ftv {Δ Γ t}:
    well_scoped Δ Γ t ->
    ftv t ⊆ Δ.
  Admitted.

  Lemma well_scoped_unique { Δ Γ t } :
    well_scoped Δ Γ t ->
    unique_open Δ Γ t ->
    disjoint Γ (bound_vars t).
  Admitted.

  Lemma elim_unique {t t'} :
    elim t t' ->
    unique t  ->
    unique t'.
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

Definition unique_inv t :=
  unique t /\
  disjoint (fv t) (bound_vars t) /\
  disjoint (ftv t) (btv t).

Lemma elim_unique_disjoint rec bs t bs' t' :
  (* From elim_delete_bindings rule *)
  elim t t' ->
  elim_bindings bs bs' ->

  (* Properties on pre- and post-term*)
  unique_inv (Let rec bs' t') ->
  forall b,
    In b bs ->
    name b ∉ map name bs' ->
    disjoint (bvb b) (fv (Let rec bs' t')) /\
    disjoint (btvb b) (ftv (Let rec bs' t')).
Proof.
  intros
    elim_t_t'
    elim_bindings_bs_bs'
    unique_inv_t'
    b
    b_in_bs
    b_removed
  .
  destruct unique_inv_t' as [unique_t' [H_disjoint_term H_disjoint_ty]].
  destruct b as [ s [v ty_v] t_b | [v k] ty | [ [ty k] vs matchf cs ] ].
  all: split.

  (* TermBind bvb *)
  - simpl.
    apply Forall_singleton.
    assert (H_bound : v ∈ bound_vars (Let rec bs' t')).
      admit.
    intros H_v_in.
    unfold disjoint in H_disjoint_term.
    rewrite Forall_forall in H_disjoint_term.
    unfold not in *.
    eauto.

  (* TermBind btvb *)
  - simpl.
    constructor.

  (* TypeBind bvb *)
  - simpl.
    constructor.

  (* TypeBind btvb *)
  (* duplicate of TermBind bvb case *)
  - simpl.
    apply Forall_singleton.
    assert (H_bound : v ∈ btv (Let rec bs' t')).
    admit.
    intros H_v_in.
    unfold disjoint in H_disjoint_ty.
    rewrite Forall_forall in H_disjoint_ty.
    unfold not in *.
    eauto.

  - simpl.
Admitted.

(** For the case of removing a subset of bindings

*)
(*
    TODO: generalize return type to take into account all of
    its binders (datatypes have multiple)

      disjoint (bvb b) (fv ...) /\ disjoint (btvb b) (Annotation.fv ...)
*)
Lemma unique_well_scoped_disjoint Δ Γ rec bs t Δ' Γ' bs' t' :
  (* From elim_delete_bindings rule *)
  elim t t' ->
  elim_bindings bs bs' ->

  (* Properties on pre- and post-term*)
  unique_open Δ  Γ  (Let rec bs  t ) ->
  well_scoped Δ' Γ' (Let rec bs' t') ->
  forall b,
    In b bs ->
    name b ∉ map name bs' ->
    disjoint (bvb b) (fv (Let rec bs' t')) /\
    disjoint (btvb b) (ftv (Let rec bs' t')).
Proof.
  intros
    H_elim H_elim_bs H_unique H_ws_post
    b H_In_b_bs H_removed_b_bs.
  destruct b as [ s [v ty_v] t_b | tvd ty | dtd ]; simpl in *.

  (* TermBind *)
  - unfold disjoint.
    split.

    (* disjoint (bvb) (fv (...)) *)
    + apply Forall_singleton.
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
          admit.
          (* apply (dead_code_strengthen H_dc H_ws_pre H_ws_post) in H_v_in_Γ'.
          contradiction.
          *)
        }
      contradiction.

    (* disjoint (btvbs) (ftv (...)) *)
    + constructor.

  (* TypeBind *)
  - destruct tvd as [v k].
    split.
    + constructor.
    + apply Forall_singleton.
      intros H_In.
    assert (H_v_in_Δ' : In v Δ').
      { admit. (* similar to TermBind case *)}
    assert (H_v_no_in_Δ' : ~In v Δ').
      { admit. (* similar to TermBind case *)}
    contradiction.

  (* DatatypeBind *)
  - destruct dtd as [ [v k] vs vmatch cs].
    admit.

Admitted.
