From PlutusCert Require Import
  PlutusIR.


Definition arity (f : DefaultFun) : nat :=
  match f with
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger => 2

  | EqualsInteger => 2

  | IfThenElse => 4

  | AppendByteString => 2

  (* TODO: see Plutus Core Spec *)
  | _ => 1
  end
.
