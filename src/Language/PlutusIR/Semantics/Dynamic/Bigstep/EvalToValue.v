Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Definition P_eval (t v : Term) := value v.
Definition P_eval_bindings_non_rec (t v : Term) := value v.

Lemma eval_to_value : forall t v,
    t ==> v -> value v.
Proof.
  eapply eval__ind with (P := P_eval) (P0 := P_eval_bindings_non_rec); try (intros; unfold P_eval; unfold P_eval_bindings_non_rec).
  - assumption.
  - Axiom skip : forall P, P. apply skip. (* TODO *)
  - apply V_TyAbs. assumption.
  - apply V_LamAbs.
  - assumption.
  - apply V_Constant.
  - apply V_Builtin. apply V_Builtin0. destruct f; apply PeanoNat.Nat.lt_0_succ. 
  - apply V_Builtin. assumption.
  - simpl in H5.
    destruct v1; inversion H5. {
      destruct v1_1; inversion H5. {
        destruct v1_1_1; inversion H5. {
          destruct d; inversion H5. 
          destruct v1_1_2; inversion H5.
          destruct s; inversion H5.
          destruct u; inversion H5.
          destruct v; inversion H5.
          destruct v1_2; inversion H5.
          destruct s; inversion H5.
          destruct u0; inversion H5.
          destruct v; inversion H5.
          destruct v2; inversion H5.
          destruct s; inversion H5.
          destruct u1; inversion H5.
          destruct v; inversion H5.
          apply V_Constant.
        }
        destruct v1_1_1; inversion H5.
        destruct d; inversion H5.
        destruct v1_1_2; inversion H5.
        destruct s; inversion H5.
        destruct u; inversion H5.
        destruct v; inversion H5.
        destruct u.
        - subst.
          inversion H1. subst.
          assumption.
        - subst.
          apply H3.
      }
      destruct d; inversion H5; 
        try solve [
          destruct v1_2; inversion H5;
          destruct s; inversion H5;
          destruct u; inversion H5;
          destruct v; inversion H5;
          destruct v2; inversion H5;
          destruct s; inversion H5;
          destruct u0; inversion H5;
          destruct v; inversion H5;
          apply V_Constant
        ].
    }
    destruct d; inversion H5;
      try solve [
        destruct v2; inversion H5;
        destruct s; inversion H5;
        destruct u; inversion H5;
        destruct v; inversion H5;
        apply V_Constant
      ].
  - apply V_Builtin. apply V_Builtin1_WithTyInst. apply le_S. apply le_S. apply le_n.
  - inversion H0; subst. assumption. inversion H1.
  - apply V_Error.
  - apply V_IWrap. apply H0.
  - inversion H0; subst. inversion H1. assumption.
  - assumption.
  - assumption.
Qed.