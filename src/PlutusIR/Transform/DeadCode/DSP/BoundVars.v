From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import Analysis.UniqueBinders.
From PlutusCert Require Import Semantics.Dynamic.Substitution.
From PlutusCert Require Import Semantics.Dynamic.AnnotationSubstitution.

Import UniqueBinders.Term.

Require Import Utf8_core.
Require Import Lists.List.
Require Import Strings.String.

Set Diffs "on".


Lemma bvbs_msubst : ∀ γ bs ,
  bvbs bs = bvbs <{ /[ γ /][bnr] bs }>.
Admitted.

Lemma bvbs_msubstA : ∀ ρ bs ,
  bvbs bs = bvbs <{ /[ ρ /][bnr] bs }>.
Admitted.

Lemma existsb_appears_bound_in : ∀ x bs r t,
  existsb (eqb x) (bvbs bs) = true -> Term.appears_bound_in x (Let r bs t).
Admitted.
