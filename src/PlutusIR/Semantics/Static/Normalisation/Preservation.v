From PlutusCert Require Import Util.List
  PlutusIR
  Kinding.Kinding
  Normalisation.BigStep
  SmallStep
  TypeSafety.SubstitutionPreservesTyping.SubstituteTCA
  .

(* Preservation of the reduction relation used in the normaliser *)
Axiom step_preserves_kinding_SOP_axiom : forall l Δ,
  Δ |-* (Ty_SOP l) : Kind_Base.

(* TODO: We ended up not needing it for normalisation_preserves_kinding because we moved through normalise instead of normaliser*)
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



(* TODO: See also TypeLanguage/Preservation *)
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
