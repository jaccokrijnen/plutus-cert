Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Definition P_value (v : Term) := v ==> v.
Definition P_value_builtin (v : Term) := v ==> v.

Lemma eval_value : forall v,
    value v -> 
    P_value v.
Proof.
  apply value__ind with (P := P_value) (P0 := P_value_builtin).
  - (* V_TyAbs *) 
    intros. unfold P_value.
    apply E_TyAbs.
  - (* V_LamAbs *)
    intros. unfold P_value.
    apply E_LamAbs.
  - (* V_Constant *)
    intros. unfold P_value.
    apply E_Constant.
  - (* V_Builtin *)
    intros. unfold P_value.
    assumption.
  - (* V_Error *)
    intros. unfold P_value.
    apply E_Error.
  - (* V_IWrap *)
    intros. unfold P_value.
    apply E_IWrap.
    assumption.
  - (* V_IfTyInst *)
    intros. unfold P_value.
    apply E_IfTyInst.
    apply E_Builtin.
  - (* V_IfCondition *)
    intros. unfold P_value.
    apply E_IfCondition.
    + apply E_IfTyInst.
      apply E_Builtin.
    + apply E_Constant.
  - (* V_IfThenBranch *)
    intros. unfold P_value.
    apply E_IfThenBranch.
    apply E_IfCondition.
    * apply E_IfTyInst.
      apply E_Builtin.
    * apply E_Constant.

  - (* V_Builtin0 *)
    intros. unfold P_value_builtin.
    apply E_Builtin.
  - (* V_Builtin1 *)
    intros. unfold P_value_builtin.
    apply E_ApplyBuiltin1.
    + apply E_Builtin.
    + apply V_Builtin0.
      apply PeanoNat.Nat.lt_succ_l.
      assumption.
    + assumption.
    + apply V_Builtin1.
      * assumption.
      * assumption.
  - (* V_Builtin2 *)
    intros. unfold P_value_builtin.
    apply E_ApplyBuiltin1.
    + apply E_ApplyBuiltin1.
      * apply E_Builtin.
      * apply V_Builtin0.
        apply PeanoNat.Nat.lt_succ_l.
        apply PeanoNat.Nat.lt_succ_l.
        assumption.
      * assumption.
      * apply V_Builtin1.
        -- apply PeanoNat.Nat.lt_succ_l.
           assumption.
        -- assumption.
    + apply V_Builtin1.
      * apply PeanoNat.Nat.lt_succ_l.
        assumption.
      * assumption.
    + assumption.
    + apply V_Builtin2.
      * assumption.
      * assumption.
      * assumption.  
Qed.