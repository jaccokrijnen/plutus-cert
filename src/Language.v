Require Import Utf8_core.
Require Import ZArith.BinInt.

Record Language : Type :=
  { expr : Type
  ; bigstep : expr -> expr -> Prop
  ; app : expr -> expr -> expr
  ; const : Z -> expr
  }.

(* Run a program p in language L *)
Definition run L p (n r : Z) :=
  bigstep L (app L p (const L n)) (const L r).

Definition forward L1 L2 (p1 : expr L1) (p2 : expr L2) :=
  ∀ n r, run L1 p1 n r -> run L2 p2 n r
.
