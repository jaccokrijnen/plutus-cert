Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.


Ltac invert_neutrals :=
  match goal with
  | H : unsaturated_with ?n ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  | H : unsaturated ?t |- False =>
      inversion H; clear H; subst; try invert_neutrals
  end.

Ltac decide_unsaturated :=
  match goal with
  | |- unsaturated ?nv =>
      unfold unsaturated; econstructor; simpl; eauto; try decide_unsaturated
  | |- unsaturated_with ?n ?nv =>
      econstructor; simpl; eauto; try decide_unsaturated
  | |- ?f <> ?f' =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  | |- ~ unsaturated ?t =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; invert_neutrals]
  | |- ~ is_error ?t =>
      let Hcon := fresh "Hcon" in
      try solve [intros Hcon; inversion Hcon]
  end.

Import PlutusNotations.

Definition Ty_int : ty := Ty_Builtin DefaultUniInteger.
Definition int_and_int_to_int : ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).

Example test_ifThenElse : forall x y, exists k,
  <{
    (λ x :: ℤ → ℤ → ℤ, {Var x} ⋅ Int 17 ⋅ Int 3)
      ⋅ ((λ y :: ℤ, ifthenelse) ⋅ Int 666 @ ℤ ⋅ true)
  }>
      =[k]=> <{ Int 17 }>.
Proof with (eauto with hintdb__eval_no_error || (try solve [decide_unsaturated])).
  unfold constInt.
  intros.
  eexists.
  eapply E_Apply...
  - eapply E_NeutralApplyPartial...
    + eapply E_NeutralTyInstPartial...
      * eapply E_Apply...
      * simpl...
      * eapply E_NeutralTyInst...
    + simpl...
    + eapply E_NeutralApply...
  - simpl...
  - simpl. rewrite eqb_refl.
    eapply E_NeutralApplyFull...
    repeat econstructor...
Qed.
