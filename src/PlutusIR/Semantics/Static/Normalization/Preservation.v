From PlutusCert Require Import Util.List
  PlutusIR
  Kinding.Kinding
  Normalization.BigStep
  SmallStep
  TypeSafety.SubstitutionPreservesTyping.SubstituteTCA
  .

(* ADMITTED: Time constraints *)
Axiom step_preserves_kinding_SOP_axiom : forall l Δ,
  Δ |-* (Ty_SOP l) : Kind_Base.

(* Preservation of PIR type system's small step reduction relation. *)
Theorem step_preserves_kinding {T T'} : forall Δ K,
  Δ |-* T : K -> step T T' -> Δ |-* T' : K.
Proof.
  intros.
  generalize dependent K.
  generalize dependent Δ.
  induction H0; intros Δ K0 Hkind_T; 
    inversion Hkind_T; subst; try solve [econstructor; eauto].
  - inversion H2; subst.
    eapply substituteTCA_preserves_kinding; eauto.
  - apply step_preserves_kinding_SOP_axiom.
Qed.

(* Normalization preserves kinds and contexts *)
Theorem normalisation_preserves_kinding {Δ T Tn K } :
  Δ |-* T : K -> normalise T Tn -> Δ |-* Tn : K.
Proof.
  intros.
  generalize dependent K.
  generalize dependent Δ.
  induction H0; intros Δ K0 Hkind; inversion Hkind; subst; try solve [econstructor; eauto].
  - eapply IHnormalise3; eauto.
    eapply substituteTCA_preserves_kinding; eauto.
    specialize (IHnormalise1 Δ (Kind_Arrow K1 K0) H2).
    inversion IHnormalise1; subst.
    assumption.
  - (* ADMIT: Unimplemented Ty_SOP*)
    admit.
Admitted.
