From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Semantics.Static.Typing.
From PlutusCert Require Import PlutusIR.Semantics.Dynamic.Bigstep.

Require Import Lists.List.
Import ListNotations.

Definition eval' t r := exists j, eval t r j.
Definition succeeds t r := eval' t r /\ value r.
Notation "t '==>' r" := (eval' t r) (at level 20).
Notation "t '==>e'" := (exists T, eval' t (Error T)) (at level 20).

Definition val_unit : term :=
  Constant (ValueOf DefaultUniUnit tt)
.

Definition ty_validator : ty :=
  Ty_Fun
    (Ty_Builtin DefaultUniData)
    (Ty_Builtin DefaultUniUnit)
.

Definition validator_equivalent s t :=
  ([],, [] |-+ s : ty_validator) /\
  ([],, [] |-+ t : ty_validator) /\
  forall (d : Data) i,
    i = Constant (ValueOf DefaultUniData d) ->
      (Apply s i ==> val_unit <-> Apply t i ==> val_unit) /\
      (Apply s i ==>e <-> Apply t i ==>e)
.

Notation "s '=val' t" := (validator_equivalent s t)
  ( at level 70
  , no associativity).

Lemma validator_value t r :
  [],, [] |-+ t : ty_validator ->
  t ==> r ->
  r = val_unit \/ is_error r.
Proof.
(* TODO: follows from type preservation and result *)
Admitted.

Module Equivalence.

  Lemma refl t : [] ,, [] |-+ t : ty_validator -> t =val t.
  Proof.
    unfold validator_equivalent.
    intuition.
  Qed.

  Lemma sym s t : s =val t -> t =val s.
  Proof.
    unfold validator_equivalent.
    intuition.
  Qed.

  Lemma trans s t u : s =val t -> t =val u -> s =val u.
  Proof.
    unfold validator_equivalent.
    intuition.
  Qed.

End Equivalence.
