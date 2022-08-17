From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
.

Lemma compatibility_C_Apply_R : forall Δ₁ Γ₁ C1 C2 Δ Γ T T₁ T₂ e1 e2,
  LR_logically_approximate Δ₁ Γ₁ e1 e2 (Ty_Fun T₁ T₂) ->
  LR_logically_approximate_context Δ₁ Γ₁ C1 C2 Δ Γ T T₁ ->
  LR_logically_approximate_context Δ₁ Γ₁ (C_Apply_R e1 C1) (C_Apply_R e2 C2) Δ Γ T T₂.
Admitted.

