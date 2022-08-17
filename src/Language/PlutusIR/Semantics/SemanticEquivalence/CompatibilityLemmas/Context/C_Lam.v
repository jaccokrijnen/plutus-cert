From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
  Normalisation
  Util.Map
.

Lemma compatibility_C_LamAbs : forall Δ₁ Γ₁ v C1 C2 Δ Γ T T₁ T₁n T₂,
  normalise T₁ T₁n ->
  LR_logically_approximate_context Δ₁ (v |-> T₁n ; Γ₁) C1 C2 Δ Γ T T₂ ->
  LR_logically_approximate_context Δ₁ Γ₁ (C_LamAbs v T₁ C1) (C_LamAbs v T₁ C2) Δ Γ T (Ty_Fun T₁n T₂).
Admitted.


