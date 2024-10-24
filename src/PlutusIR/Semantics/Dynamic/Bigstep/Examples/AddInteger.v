Require Import PlutusCert.PlutusIR.
Import PlutusNotations.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_to_int : ty := Ty_Fun Ty_int Ty_int.



Example test_addInteger : forall x, exists k,
  <{ (λ x :: (ℤ → ℤ), {Var x} ⋅ CInt 17) ⋅ ({Builtin AddInteger} ⋅ CInt 3) }>
  =[k]=> <{ CInt 20}>.
Proof with (autounfold; eauto with hintdb__eval_no_error || (try solve [intros Hcon; inversion Hcon])).
  intros.
  eexists.
  eapply E_Apply...
  -
  match goal with
    | |- fully_applied ?t -> False => assert (H := fully_applied_dec t)
  end.
  decide H.
  +



  not_fully_applied.
  - eapply E_Apply...
    + not_fully_applied.
    + apply E_Builtin_Eta with (f := AddInteger).
    + cbv.
      constructor.
  - intros Hcon.
    inversion Hcon.
  - simpl.
    rewrite eqb_refl.
    eapply E_Apply...
    not_fully_applied.
    simpl.
    eapply E_Builtin_Apply...
    unfold fully_applied.
    exists AddInteger.
    apply FA_Apply...
    apply FA_Apply...
    apply FA_Builtin...
Qed.
