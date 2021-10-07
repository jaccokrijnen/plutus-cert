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

Example test_addInteger : forall x, exists k,
  Apply (LamAbs x int_to_int (Apply (Var x) (constInt 17))) (Apply (Builtin AddInteger) (constInt 3))
  =[k]=> constInt 20.
Proof.
  intros.
  eexists.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyExtBuiltin.
    + apply E_Builtin.
      intros Hcon.
      discriminate.
    + apply E_Constant.
    + apply E_ExtBuiltinPartiallyApplied.
      auto.
  - simpl.
    rewrite eqb_refl.
    eapply E_ApplyExtBuiltin.
    + eapply E_ExtBuiltinPartiallyApplied.
      auto.
    + apply E_Constant.
    + apply E_ExtBuiltinFullyApplied.
      all: auto.
Qed.