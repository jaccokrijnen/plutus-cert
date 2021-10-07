Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_DatatypeBind : forall Delta Gamma d,
    (Delta, Gamma) |-ok (DatatypeBind d) ->
    LR_logically_approximate_binding Delta Gamma (DatatypeBind d) (DatatypeBind d).
Proof with eauto_LR.
  intros Delta Gamma d Hok.
  unfold LR_logically_approximate_binding.

  split...
Qed.