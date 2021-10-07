Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Definition P_value (v : Term) := v =[0]=> v.
Definition P_value_builtin (v : Term) := v =[0]=> v.
#[export] Hint Unfold P_value P_value_builtin : core.

Lemma eval_value : forall v,
    value v -> 
    P_value v.
Proof.
  induction 1; intros; autounfold.
  - (* V_TyAbs *) 
    apply E_TyAbs.
  - (* V_LamAbs *)
    apply E_LamAbs.
  - (* V_Constant *)
    apply E_Constant.
  - (* V_Error *)
    apply E_Error.
  - (* V_IWrap *)
    apply E_IWrap.
    assumption.
  - (* V_If *)
    apply E_If.
  - (* V_IfTyInst *)
    apply E_IfTyInst.
    apply E_If.
  - (* V_IfCondition *)
    replace 0 with (0 + 0) by reflexivity.
    apply E_IfCondition.
    + apply E_IfTyInst.
      apply E_If.
    + apply E_Constant.
  - (* V_IfThenBranch *)
    apply E_IfThenBranch.
    replace 0 with (0 + 0) by reflexivity.
    apply E_IfCondition.
    * apply E_IfTyInst.
      apply E_If.
    * apply E_Constant.
  - (* ExtBuiltin *)
    intros. unfold P_value_builtin.
    apply E_ExtBuiltinPartiallyApplied.
    assumption.
Qed.