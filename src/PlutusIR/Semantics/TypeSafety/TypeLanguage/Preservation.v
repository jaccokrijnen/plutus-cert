Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

From Coq Require Import Program.Equality.

Theorem preservation : forall Δ T K Tn,
    Δ |-* T : K ->
    normalise T Tn ->
    Δ |-* Tn : K.
Proof.
    intros Δ T K Tn Hkind_T Hnorm.
    generalize dependent K.
    generalize dependent Δ.
    induction Hnorm; intros.
    - (* N_BetaReduce *)
      dependent destruction Hkind_T; subst.
      eapply IHHnorm3.
      eapply substituteTCA_preserves_kinding.
      + eapply IHHnorm1 in Hkind_T1.
        inversion Hkind_T1; subst.
        eauto.
      + eapply IHHnorm2; eauto.
    - (* N_TyApp *)
      dependent destruction Hkind_T; subst.
      econstructor.
      + eapply IHHnorm1; eauto.
      + eapply IHHnorm2; eauto. 
    - (* N_TyFun *)
      dependent destruction Hkind_T; subst.
      econstructor.
      + eapply IHHnorm1; eauto.
      + eapply IHHnorm2; eauto.
    - (* N_TyForall *)
      dependent destruction Hkind_T; subst.
      econstructor.
      eapply IHHnorm; eauto.
    - (* N_TyLam *)
        dependent destruction Hkind_T; subst.
        econstructor.
        eapply IHHnorm; eauto.
    - (* N_TyVar *)
        dependent destruction Hkind_T; subst.
        constructor.
        assumption.
    - (* N_TyIFix *)
        dependent destruction Hkind_T; subst.
        econstructor.
        + eapply IHHnorm2; eauto.
        + eapply IHHnorm1; eauto.
    - (* N_TyBuiltin *)
        dependent destruction Hkind_T; subst.
        constructor.
        assumption.
    - (* N_TySOP *) 
       (* ADMIT: TySOP unimplemented *)
       admit.
Admitted.