(*
Soundness proof based on Section 2.4 (Theorem 2.7)
*)
From PlutusCert Require Import
  PlutusIR.Semantics.Static
  PlutusIR.Semantics.Dynamic
  PlutusIR.Semantics.SemanticEquivalence.Contextual
  PlutusIR.Semantics.SemanticEquivalence.LogicalRelation
  PlutusIR.Semantics.SemanticEquivalence.Contextual
  PlutusIR.Semantics.SemanticEquivalence.FundamentalProperty
  .

Require Import Lists.List.
Import ListNotations.

Ltac destruct_hypos := repeat (match goal with
  | H : exists a, _ |- _ => destruct H
  | H : ?x /\ ?y |- _ => destruct H
  end).


Theorem LR_sound : forall Δ Γ e e' T,
  LR_logically_approximate Δ Γ e e' T ->
  Δ ,, Γ |- e ≤-ctx e' : T.
Proof with eauto.
  intros Δ Γ e e' T H_approx_e_e'.
  unfold contextually_approximate.
  repeat split.

  1,2:
    unfold LR_logically_approximate in *;
    destruct_hypos;
    auto.


  intros C H_C_Ty H_C_e_terminates.
  destruct H_C_e_terminates as [j H_steps_C_e].

  (* apply fundamental theorem of contexts (reflexivity) *)
  apply LR_reflexivity_context in H_C_Ty as H_approx_C_C.

  unfold LR_logically_approximate_context in *.
  assert (H_approx_C_e_C_e' := H_approx_C_C _ _ H_approx_e_e').
  clear H_approx_C_C.

  unfold LR_logically_approximate in H_approx_C_e_C_e'.
  repeat (apply proj2 in H_approx_C_e_C_e').
  assert (H_RC_C_e_C_e' := H_approx_C_e_C_e' (S j) nil nil nil RD_nil (RG_nil _ _)).
  clear H_approx_C_e_C_e'.
  simpl in H_RC_C_e_C_e'.

  autorewrite with RC in *.

  assert (H4 := H_RC_C_e_C_e' _ (PeanoNat.Nat.lt_succ_diag_r j) _ H_steps_C_e).
  clear H_RC_C_e_C_e'.

  unfold terminates.
  destruct_hypos...
  simpl in H2.
  intuition.
  - destruct H7 as [k [k' [H_eq1 [H_eq2 H_eq3]]]].
    subst.
    rewrite <- H_eq3 in H.
    eexists x0.
    eauto.
  - inversion H2.
Qed.

Corollary LR_equivalent_sound : forall Δ Γ e e' T,
  LR_logically_equivalent Δ Γ e e' T ->
  Δ ,, Γ |- e =ctx e' : T.
Proof with eauto using LR_sound.
  intros Δ Γ e e' T H.
  unfold LR_logically_equivalent in H.
  destruct_hypos.
  split...
Qed.
