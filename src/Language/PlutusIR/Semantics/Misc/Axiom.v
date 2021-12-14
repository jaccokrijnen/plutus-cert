Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Language.PlutusIR.Semantics.Misc.BoundVars.
Require Export PlutusCert.Language.PlutusIR.Semantics.Misc.UniqueBinders.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Axiom uniqueness : forall t, Term.unique t.

Axiom uniqueness' : forall (Delta : Delta) e,
  forall X,
    Annotation.appears_bound_in X e ->
    Delta X = None.