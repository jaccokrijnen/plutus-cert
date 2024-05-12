Require Import PlutusCert.PlutusIR.

Require Export PlutusCert.PlutusIR.Analysis.BoundVars.
Require Export PlutusCert.PlutusIR.Analysis.UniqueBinders.
Require Import PlutusCert.PlutusIR.Semantics.Static.

Axiom uniqueness : forall t, unique_tm t.

Axiom uniqueness' : forall (Delta : Delta) e,
  forall X,
    appears_bound_in_ann X e ->
    Delta X = None.
