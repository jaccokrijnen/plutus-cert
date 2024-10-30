From PlutusCert Require Import
  PlutusIR
  Bigstep
  Util.
Import PlutusNotations.


Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_to_int : ty := Ty_Fun Ty_int Ty_int.



Ltac dec_fully_applied :=
  match goal with
    | |- ~ fully_applied ?t =>
           assert (H := sumboolOut (fully_applied_dec t));
           assumption
    | |- fully_applied ?t =>
           assert (H := sumboolOut (fully_applied_dec t));
           assumption
  end.

Example test_addInteger : forall x, exists k,
  <{ (λ x :: (ℤ → ℤ), {Var x} ⋅ CInt 17) ⋅ ({Builtin AddInteger} ⋅ CInt 3) }>
  =[k]=> <{ CInt 20}>.
Proof.
(* Proof with (autounfold; eauto with hintdb__eval_no_error || (try solve [intros Hcon; inversion Hcon])). *)
  intros.
  eexists.
  eapply E_Apply...
  - dec_fully_applied.
  - apply E_LamAbs.
  - eapply E_Apply...
    + dec_fully_applied.
    + apply E_Builtin_Eta with (f := AddInteger).
    + apply E_Constant.
    + inversion 1.
    + apply E_LamAbs.
  - simpl.
    inversion 1.
  - simpl.
    rewrite eqb_refl.
    eapply E_Apply.
    + dec_fully_applied.
    + apply E_LamAbs.
    + apply E_Constant.
    + inversion 1.
    + simpl.
      apply E_Builtin_Apply.
      * dec_fully_applied.
      * reflexivity.
Qed.
