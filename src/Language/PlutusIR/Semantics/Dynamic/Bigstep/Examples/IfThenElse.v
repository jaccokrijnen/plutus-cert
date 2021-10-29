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
Proof with eauto.
  unfold constInt.
  intros.
  eexists.
  eapply E_Apply... { 
    eapply E_IfCondition...
    eapply E_IfTyInst...
    eapply E_Apply...
    intros Hcon.
    inversion Hcon.
  } {
    intros Hcon.
    inversion Hcon.
  }
  simpl.
  rewrite eqb_refl...
Qed.