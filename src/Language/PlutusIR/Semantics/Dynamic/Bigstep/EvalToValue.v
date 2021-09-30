Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.


Lemma compute_defaultfun__to_value : forall t v,
    compute_defaultfun t = Datatypes.Some v ->
    value v.
Proof.
  intros.
  destruct t; try discriminate.
  simpl in H.
  destruct t1; try discriminate.
  - destruct t1_1; try discriminate.
    + destruct t1_1_1; try discriminate.
      destruct d; try discriminate.
      destruct t1_1_2; try discriminate.
      destruct s; try discriminate.
      destruct u; try discriminate.
      destruct v0; try discriminate.
      destruct t1_2; try discriminate.
      destruct s; try discriminate.
      destruct u0; try discriminate.
      destruct v0; try discriminate.
      destruct t2; try discriminate.
      destruct s; try discriminate.
      destruct u1; try discriminate.
      destruct v0; try discriminate.
      inversion H. subst.
      constructor.
    + destruct d; try discriminate.
      all: try solve [
        destruct t1_2; try discriminate;
        destruct s; try discriminate;
        destruct u; try discriminate;
        destruct v0; try discriminate;
        destruct t2; try discriminate;
        destruct s; try discriminate;
        destruct u0; try discriminate;
        destruct v0; try discriminate;
        inversion H; subst; constructor
      ].
  - destruct d; try discriminate.
    all: try solve [
      destruct t2; try discriminate;
      destruct s; try discriminate;
      destruct u; try discriminate;
      destruct v0; try discriminate;
      inversion H; subst; constructor
    ].
Qed.

Definition P_eval (t v : Term) (k : nat) := value v.
Definition P_eval_bindings_nonrec (t v : Term) (k : nat) := value v.
Definition P_eval_bindings_rec (bs0 : list Binding) (t v : Term) (k : nat) := value v.

Lemma eval_to_value : forall t v k,
    t =[k]=> v -> value v.
Proof.
  eapply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec); 
    try (intros; unfold P_eval; unfold P_eval_bindings_nonrec; unfold P_eval_bindings_rec).
  - assumption.
  - assumption.
  - apply V_TyAbs.
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
  - apply V_IfTyInst.
  - apply V_IfCondition.
  - apply V_IfThenBranch.
  - assumption.
  - assumption.
  - assumption.
  - apply V_Error.
  - apply V_IWrap. apply H0.
  - inversion H0; subst. inversion H1. assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.