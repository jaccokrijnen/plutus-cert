Require Import PlutusCert.Language.PlutusIR.
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

Definition constInt (a : Z) : Term := (Constant (@Some valueOf DefaultUniInteger (ValueOf DefaultUniInteger a))).
Definition constBool (a : bool) : Term := Constant (Some (ValueOf DefaultUniBool a)).
Definition constBS (a : string) : Term := Constant (Some (ValueOf DefaultUniByteString a)).
Definition constChar (a : ascii) : Term := Constant (Some (ValueOf DefaultUniChar a)).
Definition constString (a : string) : Term := Constant (Some (ValueOf DefaultUniString a)).
Definition constUnit (a : unit) : Term := Constant (Some (ValueOf DefaultUniUnit a)).

Definition take (x : Z) (s : string) : string := substring 0 (Z.to_nat x) s.
Definition drop (x : Z) (s : string) : string := substring (Z.to_nat x) (length s) s.

(** Computes results of fully applied default functions where possible.
    
    Note that not all default functions have sensible implementations, such
    as SHA2, SHA3 and VerifySignature. This is bound to change in the future.
*)
Definition compute_defaultfun (t : Term) : option Term :=
  match t with
  (** Binary operators on integers *)
  (* AddInteger *)
  | ExtBuiltin AddInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x + y))
  (* SubtractInteger *)
  | ExtBuiltin SubtractInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x - y))
  (* MultiplyInteger *)
  | ExtBuiltin MultiplyInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x * y))
  (* DivideInteger *)
  | ExtBuiltin DivideInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x / y))
  (* QuotientInteger *)
  | ExtBuiltin QuotientInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x ÷ y))
  (* RemainderInteger *)
  | ExtBuiltin RemainderInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ]
      => Datatypes.Some (constInt (Z.rem x y))
  (* ModInteger *)
  | ExtBuiltin ModInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constInt (x mod y))
  (** Binary predicates on integers *)
  (* LessThanInteger*)
  | ExtBuiltin LessThanInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constBool (x <? y))
  (* LessThanEqInteger *)
  | ExtBuiltin LessThanEqInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constBool (x <=? y))
  (* GreaterThanInteger *)
  | ExtBuiltin GreaterThanInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constBool (x >? y))
  (* GreaterThanEqInteger *)
  | ExtBuiltin GreaterThanEqInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constBool (x >=? y))
  (* EqInteger *)
  | ExtBuiltin EqInteger 
      [ Constant (@Some _ DefaultUniInteger (ValueOf _ y)) 
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ] 
      => Datatypes.Some (constBool (x =? y))
  (** Bytestring operations *)
  (* Concatenate *)
  | ExtBuiltin Concatenate
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs2))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ bs1))
      ]
      => Datatypes.Some (constBS (bs1 ++ bs2))
  (* TakeByteString *)
  | ExtBuiltin TakeByteString
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ]
      => Datatypes.Some (constBS (take x bs))
  (* DropByteString *)
  | ExtBuiltin DropByteString
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs))
      ; Constant (@Some _ DefaultUniInteger (ValueOf _ x))
      ]
      => Datatypes.Some (constBS (drop x bs))
  (** Bytestring hashing
      
      Note: We model hashing by identity. Comparing hashes now becomes a straightforward equality check.
      We believe modelling hash function as such is sufficient, because the dynamic semantics is not meant to 
      be used as a basis for a real-world evaluator.
  *)
  | ExtBuiltin SHA2
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs))
      ]
      => Datatypes.Some (constBS bs)
  | ExtBuiltin SHA3
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs))
      ]
      => Datatypes.Some (constBS bs)
  (** Signature verification 
      
      TODO: Obviously, this should evaluate to true. However, how can we model the verification of signatures? 
      Implementation of signature verification:
      https://input-output-hk.github.io/ouroboros-network/cardano-crypto/Crypto-ECC-Ed25519Donna.html
  *)
  | ExtBuiltin VerifySignature
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ signature))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ message))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ publicKey))
      ]
      => Datatypes.Some (constBool true)
  (** Binary predicates on bytestrings *)
  (* EqByteString *)
  | ExtBuiltin EqByteString
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs2))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ bs1))
      ]
      => Datatypes.Some (constBool (bs1 =? bs2)%string)
  (* LtByteString *)
  | ExtBuiltin LtByteString
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs2))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ bs1))
      ]
      => Datatypes.Some (constBool (to_Z bs1 <? to_Z bs2))
  (* GtByteString *)
  | ExtBuiltin GtByteString
      [ Constant (@Some _ DefaultUniByteString (ValueOf _ bs2))
      ; Constant (@Some _ DefaultUniByteString (ValueOf _ bs1))
      ]
      => Datatypes.Some (constBool (to_Z bs1 >? to_Z bs2))
  (* String operations *)
  (* CharToString *)
  | ExtBuiltin CharToString
      [ Constant (@Some _ DefaultUniChar (ValueOf _ ch))
      ]
      => Datatypes.Some (constString (String ch EmptyString))
  (* Append *)
  | ExtBuiltin Append
      [ Constant (@Some _ DefaultUniString (ValueOf _ s2))
      ; Constant (@Some _ DefaultUniString (ValueOf _ s1))
      ]
      => Datatypes.Some (constString (s1 ++ s2))
  (* Trace *)
  | ExtBuiltin Trace
      [ Constant (@Some _ DefaultUniString (ValueOf _ s))
      ] 
      => Datatypes.Some (constUnit tt)
  (* Catch-all: The argument term is not a fully applied builtin *)
  | _ => None
  end.