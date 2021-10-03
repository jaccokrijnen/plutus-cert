Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Lemma compatibility_DatatypeBind : forall Delta Gamma d,
    LR_logically_approximate_binding Delta Gamma (DatatypeBind d) (DatatypeBind d).
Proof.
  intros Delta Gamma d.
  unfold LR_logically_approximate_binding.
Admitted.