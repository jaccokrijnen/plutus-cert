From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
.

Lemma compatibility_C_Apply_L : forall Δ₁ Γ₁ C1 C2 Δ Γ T T₁ T₂ e1 e2,
  LR_logically_approximate_context Δ₁ Γ₁ C1 C2 Δ Γ T (Ty_Fun T₁ T₂) ->
  LR_logically_approximate Δ₁ Γ₁ e1 e2 T₁ ->
  LR_logically_approximate_context Δ₁ Γ₁ (C_Apply_L C1 e1) (C_Apply_L C2 e2) Δ Γ T T₂.
Admitted.


