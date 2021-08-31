Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.Deterministic.

Lemma eval_congr_Apply1 : forall t1 t2 v1 v0,
    Apply t1 t2 ==> v0 ->
    t1 ==> v1 ->
    Apply v1 t2 ==> v0.
Proof.
  intros.
  inversion H; subst.
  - assert (v1 = LamAbs x T t4) by (eapply eval__deterministic; eauto).
    subst.
    apply E_Apply with x T t4 t0' v2.
    + apply E_LamAbs.
    + assumption.
    + assumption.
    + assumption.
  - assert (v1 = v2) by (eapply eval__deterministic; eauto).
    subst.
    apply E_ApplyBuiltin1.
    + apply eval_value.
      apply V_Builtin.
      assumption.
    + assumption.
    + assumption.
    + assumption.
  - assert (v1 = v2) by (eapply eval__deterministic; eauto).
    subst.
    eapply E_ApplyBuiltin2.
    + apply eval_value.
      apply V_Builtin.
      assumption.
    + assumption.
    + apply H5.
    + assumption.
    + assumption.
  - assert (v1 = TyInst (Builtin IfThenElse) T) by (eapply eval__deterministic; eauto).
    subst.
    eapply E_IfCondition.
    + apply eval_value.
      apply V_IfTyInst.
    + assumption.
  - assert (v1 = Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))) by (eapply eval__deterministic; eauto).
    subst.
    apply E_IfThenBranch.
    apply E_IfCondition.
    + apply E_IfTyInst.
      apply E_Builtin.
    + apply E_Constant.
  - assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t) by (eapply eval__deterministic; eauto).
    subst.
    eapply E_IfTrue.
    + apply E_IfThenBranch.
      apply E_IfCondition.
      * apply E_IfTyInst.
        apply E_Builtin.
      * apply E_Constant.
    + assumption.
  - assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t) by (eapply eval__deterministic; eauto).
    subst.
    eapply E_IfFalse.
    + apply E_IfThenBranch.
      apply E_IfCondition.
      * apply E_IfTyInst.
        apply E_Builtin.
      * apply E_Constant.
    + assumption.
Qed.
