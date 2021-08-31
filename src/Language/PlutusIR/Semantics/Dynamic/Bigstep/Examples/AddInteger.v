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
Definition int_to_int : Ty := Ty_Fun Ty_int Ty_int.

Example test_addInteger : forall x,
  Apply (LamAbs x int_to_int (Apply (Var x) (constInt 17))) (Apply (Builtin AddInteger) (constInt 3))
  ==> constInt 20.
Proof.
  intros.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyBuiltin1.
    + apply E_Builtin.
    + apply V_Builtin0.
      simpl.
      apply le_S.
      apply le_n.
    + apply E_Constant.
    + apply V_Builtin1.
      * simpl.
        apply le_n.
      * apply V_Constant.
  - apply S_Apply.
    + apply S_Var1.
    + apply S_Constant.
  - eapply E_ApplyBuiltin2.
    + eapply E_ApplyBuiltin1.
      * apply E_Builtin.
      * apply V_Builtin0.
        simpl.
        apply le_S.
        apply le_n.
      * apply E_Constant.
      * apply V_Builtin1.
        -- simpl.
           apply le_n.
        -- apply V_Constant.
    + apply V_Builtin1.
      -- apply le_n.
      -- apply V_Constant.
    + apply E_Constant.
    + intros Hcon.
      inversion Hcon. subst.
      simpl in H2.
      apply PeanoNat.Nat.lt_irrefl in H2.
      inversion H2. 
    +  reflexivity.
Qed.