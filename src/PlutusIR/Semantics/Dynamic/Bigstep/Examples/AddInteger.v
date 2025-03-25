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
From Coq Require Import Lia.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_to_int : ty := Ty_Fun Ty_int Ty_int.


Lemma partial_plus : <{ (+) ⋅ CInt 3 }> =[ 0 ]=> <{ (+) ⋅ CInt 3}>.
Proof with (eauto using eval).
  - eapply E_Apply_Builtin_Partial with (j0 := 0%nat)...
    + econstructor...
    + econstructor... unfold args_len, arity. lia.
Qed.

Example test_addInteger : forall x, exists k,
  <{ (λ x :: (ℤ → ℤ), {Var x} ⋅ CInt 17) ⋅ ({Builtin AddInteger} ⋅ CInt 3) }>
  =[k]=> <{ CInt 20}>.
Proof with (eauto using eval).
(* Proof with (autounfold; eauto with hintdb__eval_no_error || (try solve [intros Hcon; inversion Hcon])). *)
  intros.
  eexists.
  eapply E_Apply.
  - idtac...
  - idtac...
  - apply partial_plus.
  - inversion 1.
  - simpl.
    rewrite eqb_refl.
    eapply E_Apply_Builtin_Full.
    + idtac...
    + eapply partial_plus.
    + eapply A_Apply.
      * econstructor.
      * apply A_Builtin.
    + econstructor. reflexivity.
    + econstructor.
    + unfold args_len, arity.
      lia.
    + reflexivity.
Qed.
