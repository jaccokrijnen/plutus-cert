From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Analysis.UniqueBinders.
From PlutusCert Require Import Semantics.Dynamic.Substitution.
From PlutusCert Require Import Semantics.Dynamic.AnnotationSubstitution.
From PlutusCert Require Import Multisubstitution.Congruence.

Import NamedTerm.

Import UniqueBinders.Term.

Require Import Utf8_core.
Require Import Lists.List.
Require Import Strings.String.


(* Lemmas that prove that substitution will not change the set of bound variables *)

(* Substitution does not change bound variables *)
Definition bvb_subst_b x t b :
  bvb (subst_b x t b) = bvb b
  := match b with
      | TermBind s (VarDecl y T) tb => eq_refl
      | _ => eq_refl
    end.

(* Substitution does not change bound variables *)
Definition bvb_msubst_b γ b :
  bvb (msubst_b γ b) = bvb b.
Proof.
  revert b.
  induction γ as [_ | [x t] γ] .
  - intros b. reflexivity.
  - intros b.
    simpl.
    rewrite IHγ.
    rewrite bvb_subst_b.
    reflexivity.
Qed.

Lemma msubst_bnr_nil γ :
  msubst_bnr γ nil = nil.
Proof with auto.
  induction γ.
  - reflexivity.
  - destruct a...
Qed.


(* Substitution does not change bound variables *)
Lemma bvbs_msubst_bnr γ bs :
  bvbs (msubst_bnr γ bs) = bvbs bs.
Proof with auto.
  revert γ.
  induction bs as [ | b bs].
  all: intros γ.
  - rewrite msubst_bnr_nil.
    reflexivity.
  - rewrite @bvbs_cons.
    rewrite msubst_bnr_cons.
    rewrite @bvbs_cons.
    rewrite bvb_msubst_b.
    rewrite IHbs with (γ := List.mdrop (bvb b) γ).
    reflexivity.
Qed.

Lemma bvbs_msubstA_bnr : ∀ ρ bs ,
  bvbs bs = bvbs (msubstA_bnr ρ bs).
Admitted.

Lemma existsb_appears_bound_in : ∀ x bs r t,
  existsb (eqb x) (bvbs bs) = true ->
  Term.appears_bound_in x (Let r bs t).
Admitted.
