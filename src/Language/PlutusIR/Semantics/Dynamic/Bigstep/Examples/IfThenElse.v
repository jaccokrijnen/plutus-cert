Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.


Definition Ty_int : Ty := Ty_Builtin (Some (TypeIn DefaultUniInteger)).
Definition int_and_int_to_int : Ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).

Example test_ifThenElse : forall x y, exists k,
  Apply (LamAbs x int_and_int_to_int (Apply (Apply (Var x) (constInt 17)) (constInt 3))) (Apply (TyInst (Apply (LamAbs y Ty_int (Builtin IfThenElse)) (constInt 666)) (Ty_Builtin (Some (TypeIn DefaultUniInteger)))) (Constant (Some (ValueOf DefaultUniBool true)))) =[k]=> constInt 17.
Proof.
  intros.
  eexists.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_IfCondition.
    + eapply E_IfTyInst. 
      eapply E_Apply.
      * apply E_LamAbs.
      * apply E_Constant.
      * simpl. 
        apply E_If.
    + apply E_Constant.
  - simpl.
    rewrite eqb_refl.
    eapply E_IfTrue.
    + apply E_IfThenBranch.
      * apply E_IfCondition.
        -- apply E_IfTyInst.
           apply E_If.
        -- apply E_Constant.
    + apply E_Constant.
Qed.