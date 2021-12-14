Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

From Coq Require Import Lia.



Lemma RC_lt_obsolete : forall k T rho e e',
  (0 < k -> RC k T rho e e') ->
  RC k T rho e e'.
Proof.
  intros.
  autorewrite with RC.
  intros j Hlt__j.
  assert (0 < k) by lia.
  apply H in H0.
  autorewrite with RC in H0.
  eapply H0.
  assumption.
Qed.