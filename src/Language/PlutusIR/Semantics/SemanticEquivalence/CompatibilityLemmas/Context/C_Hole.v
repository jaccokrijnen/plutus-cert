From PlutusCert Require Import
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
.


Lemma compatibility_C_Hole : forall Δ Γ T,
  LR_logically_approximate_context Δ Γ C_Hole C_Hole Δ Γ T T.
Proof with auto.
  intros.
  unfold LR_logically_approximate_context...
Qed.
