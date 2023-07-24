Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.

From Coq Require Import Lia.
  
Ltac eauto_LR :=
  try solve [eauto with typing || lia].