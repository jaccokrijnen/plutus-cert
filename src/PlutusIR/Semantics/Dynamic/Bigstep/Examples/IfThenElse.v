Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.


Ltac decide_error :=
  match goal with
  | |- ~ is_error ?t =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  end.

Import PlutusNotations.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_and_int_to_int : ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).

Example test_ifThenElse : forall x y, exists k,
  <{
    (λ x :: ℤ → ℤ → ℤ, {Var x} ⋅ CInt 17 ⋅ CInt 3)
      ⋅ ((λ y :: ℤ, ifthenelse) ⋅ CInt 666 @ ℤ ⋅ true)
  }>
      =[k]=> <{ CInt 17 }>.
Proof with (eauto with hintdb__eval_no_error || (try solve [decide_error])).
Admitted.
