(*
Soundness proof based on Section 2.4 (Theorem 2.7)
*)
From PlutusCert Require Import
  Language.PlutusIR.Semantics.Static
  Language.PlutusIR.Semantics.Dynamic
  Language.PlutusIR.Semantics.SemanticEquivalence.Contextual
  Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
  Language.PlutusIR.Semantics.SemanticEquivalence.Contextual
  Language.PlutusIR.Semantics.SemanticEquivalence.FundamentalProperty
  .

Theorem LR_sound : forall Δ Γ e e' T,
  LR_logically_approximate Δ Γ e e' T ->
  Δ ,, Γ |- e ⪯-ctx e' : T.
Proof with eauto.
  intros.
  unfold contextually_approximate.
  assert (H' := H).
  unfold LR_logically_approximate in H'.

  repeat (match goal with
    | H : ?x /\ ?y |- _ => destruct H
    | |- ?x /\ ?y => split
    end)...
  clear H2 H0 H1.

  intros.
  unfold terminates in H1.
  destruct H1 as [v [j H_Ce_v]].

  apply LR_reflexivity_context in H0.
  unfold LR_logically_approximate_context in H0.
  apply H0 in H.
  unfold LR_logically_approximate in H.
  repeat (match goal with | H : ?x /\ ?y |- _ => destruct H end).
  assert (H3 := H2 (1 + j) nil nil nil nil nil eq_refl eq_refl RD_nil (RG_nil _ _)). clear H2.
  simpl in H3.

  autorewrite with RC in H3.

  assert (H4 := H3 j (PeanoNat.Nat.lt_succ_diag_r j)). clear H3.

  apply H4 in H_Ce_v. clear H4.

  destruct H_Ce_v as [e'_f [j' [H_Ce'_v' _]]].

  unfold terminates.
  exists e'_f.
  exists j'.
  assumption.
Qed.

Corollary LR_equivalent_sound : forall Δ Γ e e' T,
  LR_logically_equivalent Δ Γ e e' T ->
  Δ ,, Γ |- e ≃-ctx e' : T.
Proof.
  intros.
  unfold LR_logically_equivalent in H.
  destruct H as [H1 H2].
  unfold contextually_equivalent.
  split; apply LR_sound; assumption.
Qed.
