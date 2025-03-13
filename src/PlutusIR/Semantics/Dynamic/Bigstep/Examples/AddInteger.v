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
Proof.
  assert (Heq : (0 = 0 + 0)%nat) by reflexivity.
  rewrite Heq.
  - eapply E_Apply_Builtin_Partial.
    + eapply E_Builtin. unfold arity. lia.
    + eapply A_Builtin.
    + econstructor.
    + econstructor.
    + unfold args_len, arity. lia.
Qed.

Example test_addInteger : forall x, exists k,
  <{ (λ x :: (ℤ → ℤ), {Var x} ⋅ CInt 17) ⋅ ({Builtin AddInteger} ⋅ CInt 3) }>
  =[k]=> <{ CInt 20}>.
Proof.
(* Proof with (autounfold; eauto with hintdb__eval_no_error || (try solve [intros Hcon; inversion Hcon])). *)
  intros.
  eexists.
  eapply E_Apply...
  - apply E_LamAbs.
  - apply partial_plus.
  - inversion 1.
  - simpl.
    rewrite eqb_refl.
    eapply E_Apply_Builtin_Full.
    + eapply partial_plus.
    + eapply A_Apply.
      * econstructor.
      * apply A_Builtin.
    + econstructor.
    + econstructor.
    + unfold args_len, arity.
      lia.
    + reflexivity.
Qed.
