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
  Util.Tactics
  .



Theorem LR_sound : forall Δ Γ e e' T,
  LR_logically_approximate Δ Γ e e' T ->
  Δ ,, Γ |- e ⪯-ctx e' : T.
Proof with eauto.
  intros Δ Γ e e' T H_approx_e_e'.
  unfold contextually_approximate.
  repeat split.

  1,2:
    unfold LR_logically_approximate in *;
    destruct_hypos;
    auto.


  intros C T₁ H_C_Ty H_C_e_terminates.
  destruct H_C_e_terminates as [v [j H_steps_C_e]].

  (* apply fundamental theorem of contexts (reflexivity) *)
  apply LR_reflexivity_context in H_C_Ty as H_approx_C_C.

  unfold LR_logically_approximate_context in *.
  assert (H_approx_C_e_C_e' := H_approx_C_C _ _ H_approx_e_e').
  clear H_approx_C_C.

  unfold LR_logically_approximate in H_approx_C_e_C_e'.
  repeat (apply proj2 in H_approx_C_e_C_e').
  assert (H_RC_C_e_C_e' := H_approx_C_e_C_e' (S j) nil nil nil nil nil eq_refl eq_refl RD_nil (RG_nil _ _)).
  clear H_approx_C_e_C_e'.
  simpl in H_RC_C_e_C_e'.

  autorewrite with RC in *.

  assert (H4 := H_RC_C_e_C_e' _ (PeanoNat.Nat.lt_succ_diag_r j) _ H_steps_C_e).
  clear H_RC_C_e_C_e'.

  unfold terminates.
  destruct_hypos...
Qed.

Corollary LR_equivalent_sound : forall Δ Γ e e' T,
  LR_logically_equivalent Δ Γ e e' T ->
  Δ ,, Γ |- e ≃-ctx e' : T.
Proof with eauto using LR_sound.
  intros Δ Γ e e' T H.
  unfold LR_logically_equivalent in H.
  destruct_hypos.
  split...
Qed.

Lemma LR_approximate_sound_ciu : forall e e' T,
  normal_Ty T ->
  empty,, empty |- e ⪯-ctx e' : T ->
  e  ⇓ ->
  e' ⇓.
Proof.
  intros e e' T H_norm_T H_approx_e_e' e_terminates.
  unfold contextually_approximate in *.
  destruct H_approx_e_e' as [H_ty_e [H_ty_e' H_steps]].
  assert (H := H_steps C_Hole T).
  eauto using context_has_type.
Qed.


Corollary LR_equivalent_sound_ciu : forall e e' T,
  normal_Ty T ->
  LR_logically_equivalent empty empty e e' T ->
  ciu_equivalent e e' T.
Proof with eauto using LR_approximate_sound_ciu.
  intros e e' T H_normal_T H.
  apply LR_equivalent_sound in H.
  assert (H' := H).
  unfold contextually_equivalent in *.
  unfold contextually_approximate in H.
  unfold ciu_equivalent.
  destruct_hypos.
  repeat split...
Qed.
