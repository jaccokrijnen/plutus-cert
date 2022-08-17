From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
.


Lemma compatibility_C_Hole : forall Δ₁ Γ₁ Δ Γ T T₁,
  LR_logically_approximate_context Δ₁ Γ₁ C_Hole C_Hole Δ Γ T T₁.
Admitted.
