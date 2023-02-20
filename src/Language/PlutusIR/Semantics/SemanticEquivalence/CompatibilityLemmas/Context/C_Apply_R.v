From PlutusCert Require Import
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
  CompatibilityLemmas.Apply
.

Lemma compatibility_C_Apply_R : forall Δ₁ Γ₁ C1 C2 Δ Γ T T₁ T₂ e1 e2,
  LR_logically_approximate Δ₁ Γ₁ e1 e2 (Ty_Fun T₁ T₂) ->
  LR_logically_approximate_context Δ₁ Γ₁ C1 C2 Δ Γ T T₁ ->
  LR_logically_approximate_context Δ₁ Γ₁ (C_Apply_R e1 C1) (C_Apply_R e2 C2) Δ Γ T T₂.
Proof.
  intros Δ₁ Γ₁ C1 C2 Δ Γ T T₁ T₂ t1 t2 H_approx_C1_C2 H_approx_t1_t2.
  unfold LR_logically_approximate_context.
  intros e1 e2 H_approx_e1_e2.

  simpl.
  eauto using compatibility_Apply.
Qed.

