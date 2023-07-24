Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.UniqueBinders.
Require Import PlutusCert.PlutusIR.Semantics.Static.

Axiom uniqueness : forall t, Term.unique t.

Axiom uniqueness' : forall (Delta : Delta) e,
  forall X,
    Annotation.appears_bound_in X e ->
    Delta X = None.
