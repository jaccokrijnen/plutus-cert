Require Import PlutusCert.PlutusIR.
Import ZArith.BinInt.
Import Coq.Lists.List.
Import Coq.Strings.String.
Import Ascii.
Require Import Coq.Strings.BinaryString.
From Equations Require Import Equations.
Import ListNotations.

Import NamedTerm.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ** Arity of built-in functions *)
Definition arity (df : DefaultFun) : nat :=
  match df with
  | AddInteger => 2
  | SubtractInteger => 2
  | MultiplyInteger => 2
  | DivideInteger => 2
  | QuotientInteger => 2
  | RemainderInteger => 2
  | ModInteger => 2
  | LessThanInteger => 2
  | LessThanEqInteger => 2
  | GreaterThanInteger => 2
  | GreaterThanEqInteger => 2
  | EqInteger => 2
  | Concatenate => 2
  | TakeByteString => 2
  | DropByteString => 2
  | SHA2 => 1
  | SHA3 => 1
  | VerifySignature => 3
  | EqByteString => 2
  | LtByteString => 2
  | GtByteString => 2
  | IfThenElse => 4
  | CharToString => 1
  | Append => 2
  | Trace => 1
  end.

(** ** Meanings of built-in functions *)

Definition constInt (a : Z) : Term := (Constant (@Some' valueOf DefaultUniInteger (ValueOf DefaultUniInteger a))).
Definition constBool (a : bool) : Term := Constant (Some' (ValueOf DefaultUniBool a)).
Definition constBS (a : string) : Term := Constant (Some' (ValueOf DefaultUniByteString a)).
Definition constChar (a : ascii) : Term := Constant (Some' (ValueOf DefaultUniChar a)).
Definition constString (a : string) : Term := Constant (Some' (ValueOf DefaultUniString a)).
Definition constUnit (a : unit) : Term := Constant (Some' (ValueOf DefaultUniUnit a)).

Definition take (x : Z) (s : string) : string := substring 0 (Z.to_nat x) s.
Definition drop (x : Z) (s : string) : string := substring (Z.to_nat x) (length s) s.

#[export] Hint Unfold
  constInt
  constBool
  constBS
  constChar
  constString
  constUnit
  take
  drop
  : core.

(** Computes results of fully applied default functions where possible.

    Note that not all default functions have sensible implementations, such
    as SHA2, SHA3 and VerifySignature. This is bound to change in the future.
*)

Notation IntConstant y := (Constant (@Some' _ DefaultUniInteger (ValueOf _  y))) (only parsing).
Notation BSConstant y := (Constant (@Some' _ DefaultUniByteString (ValueOf _  y))) (only parsing).
Notation StringConstant y := (Constant (@Some' _ DefaultUniString (ValueOf _  y))) (only parsing).
Notation BoolConstant y := (Constant (@Some' _ DefaultUniBool (ValueOf _  y))) (only parsing).
Notation CharConstant c := (Constant (@Some' _ DefaultUniChar (ValueOf _ c))) (only parsing).

Definition compute_defaultfun (t : Term) : option Term :=
  match t with
  (** Binary operators on integers *)
  (* AddInteger *)
  | Builtin AddInteger [] [IntConstant x; IntConstant y] => Some (constInt (x + y))
  (* SubtractInteger *)
  | Builtin SubtractInteger [] [IntConstant x; IntConstant y] => Some (constInt (x - y))
  (* MultiplyInteger *)
  | Builtin MultiplyInteger [] [IntConstant x; IntConstant y] => Some (constInt (x * y))
  (* DivideInteger *)
  | Builtin DivideInteger [] [IntConstant x; IntConstant y] => Some (constInt (x / y))
  (* QuotientInteger *)
  | Builtin QuotientInteger [] [IntConstant x; IntConstant y] => Some (constInt (x ÷ y))
  (* RemainderInteger *)
  | Builtin RemainderInteger [] [IntConstant x; IntConstant y] => Some (constInt (Z.rem x y))
  (* ModInteger *)
  | Builtin ModInteger [] [IntConstant x; IntConstant y] => Some (constInt (x mod y))
  (** Binary predicates on integers *)
  (* LessThanInteger*)
  | Builtin LessThanInteger [] [IntConstant x; IntConstant y] => Some (constBool (x <? y))
  (* LessThanEqInteger *)
  | Builtin LessThanEqInteger [] [IntConstant x; IntConstant y] => Some (constBool (x <=? y))
  (* GreaterThanInteger *)
  | Builtin GreaterThanInteger [] [IntConstant x; IntConstant y] => Some (constBool (x >? y))
  (* GreaterThanEqInteger *)
  | Builtin GreaterThanEqInteger [] [IntConstant x; IntConstant y] => Some (constBool (x >=? y))
  (* EqInteger *)
  | Builtin EqInteger [] [IntConstant x; IntConstant y] => Some (constBool (x =? y))
  (** Bytestring operations *)
  (* Concatenate *)
  | Builtin Concatenate [] [BSConstant bs1; BSConstant bs2] => Some (constBS (bs1 ++ bs2))
  (* TakeByteString *)
  | Builtin TakeByteString [] [IntConstant x; BSConstant bs] => Some (constBS (take x bs))
  (* DropByteString *)
  | Builtin DropByteString [] [IntConstant x; BSConstant bs] => Some (constBS (drop x bs))
  (** Bytestring hashing

      Note: We model hashing by identity. Comparing hashes now becomes a straightforward equality check.
      We believe modelling hash function as such is sufficient, because the dynamic semantics is not meant to
      be used as a basis for a real-world evaluator.
  *)
  | Builtin SHA2 [] [BSConstant bs] => Some (constBS bs)
  | Builtin SHA3 [] [BSConstant bs] => Some (constBS bs)
  (** Signature verification

      TODO: Obviously, this should evaluate to true. However, how can we model the verification of signatures?
      Implementation of signature verification:
      https://input-output-hk.github.io/ouroboros-network/cardano-crypto/Crypto-ECC-Ed25519Donna.html
  *)
  | Builtin VerifySignature [] [BSConstant publicKey; BSConstant message; BSConstant signature] =>
      Some (constBool true)
  (** Binary predicates on bytestrings *)
  (* EqByteString *)
  | Builtin EqByteString [] [BSConstant bs1; BSConstant bs2] => Some (constBool (bs1 =? bs2)%string)
  (* LtByteString *)
  | Builtin LtByteString [] [BSConstant bs1; BSConstant bs2] => Some (constBool (to_Z bs1 <? to_Z bs2))
  (* GtByteString *)
  | Builtin GtByteString [] [BSConstant bs1; BSConstant bs2] => Some (constBool (to_Z bs1 >? to_Z bs2))
  (** If-Then-Else

  TODO: The builtin If-Then-Else is strict in its branches, so they can only
  be constants. (Surface level if-then-else is translated to a case).

  The below definition is not strict and therefore breaks the proof of
  compute_defaultfun__to_value in EvalToValue.v because we don't know that the
  arguments of IfThenElse are indeed values *)

  (* | Builtin IfThenElse [_] [BoolConstant cond; thenBranch; elseBranch] => Some (if cond then thenBranch else elseBranch) *)

  (* String operations *)
  (* CharToString *)
  | Builtin CharToString [] [CharConstant ch] => Some (constString (String ch EmptyString))
  (* Append *)
  | Builtin Append [] [StringConstant s1; StringConstant s2] => Some (constString (s1 ++ s2))
  (* Trace *)
  | Builtin Trace [] [StringConstant s] => Some (constUnit tt)
  (* Catch-all: The argument term is not a fully applied builtin *)
  | _ => None
  end.
