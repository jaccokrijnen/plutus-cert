From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Analysis.UniqueBinders.
From PlutusCert Require Import Semantics.Dynamic.Substitution.
From PlutusCert Require Import Semantics.Dynamic.AnnotationSubstitution.

Import UniqueBinders.Term.

Require Import Utf8_core.
Require Import Lists.List.
Require Import Strings.String.

Set Diffs "on".



(*
Lemma msubst_cons γ b bs :
msubst_bnr γ (b :: bs) = msubst_bnr γ bs
*)

Definition bvb_subst_b x t b :
  bvb (subst_b x t b) = bvb b
  := match b with
      | TermBind s (VarDecl y T) tb => eq_refl
      | _ => eq_refl
    end.

Fixpoint bvbs_subst_bnr x t bs :
  bvbs (subst_bnr x t bs) = bvbs bs.
  refine (
    match bs with
       | nil => eq_refl
       | b :: bs => _
     end
     ).
    simpl.
    refine (
    match existsb (eqb x) (bvb b) with
      | true  => _
      | false => _
    end
    ).
    - unfold bvbs.
      rewrite map_cons.
      rewrite bvb_subst_b.
      reflexivity.
    - rewrite @bvbs_cons.
      rewrite @bvbs_cons. (* TODO, why does rewrite need @? *)

    rewrite bvbs_subst_bnr.
      rewrite bvb_subst_b.
      reflexivity.
Qed.

Lemma bvbs_msubst_bnr γ b bs :
  bvbs (msubst_bnr γ (b :: bs)) = bvb b ++ bvbs (msubst_bnr γ bs).
Proof with auto.
  induction γ as [_ | [x t] γ] .
  - simpl.
    rewrite @bvbs_cons.
    reflexivity.
  - unfold msubst_bnr.
    admit.
Admitted.

Lemma msubst_bnr_nil γ :
  msubst_bnr γ nil = nil.
Proof with auto.
  induction γ.
  - reflexivity.
  - destruct a...
Qed.

Lemma bvbs_msubst γ bs :
  bvbs bs = bvbs (msubst_bnr γ bs).
Proof with auto.
  induction bs.
  - induction γ.
    + reflexivity.
    + rewrite msubst_bnr_nil...
  - rewrite bvbs_cons.
Admitted.

Lemma bvbs_msubstA : ∀ ρ bs ,
  bvbs bs = bvbs <{ /[[ ρ /][bnr] bs }>.
Admitted.

Lemma existsb_appears_bound_in : ∀ x bs r t,
  existsb (eqb x) (bvbs bs) = true -> Term.appears_bound_in x (Let r bs t).
Admitted.
