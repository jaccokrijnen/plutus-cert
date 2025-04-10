From PlutusCert Require Import
  PlutusIR
  Util
  Builtins.Signatures
.
Import PlutusNotations.

Import ZArith.BinInt.
Import Coq.Lists.List.
Import Coq.Strings.String.
Import Coq.Bool.Bool.
Import Coq.Strings.Byte.
Import Ascii.
Require Import Coq.Strings.BinaryString.
From Equations Require Import Equations.
Import ListNotations.

Local Open Scope Z_scope.


Section Eta.
  (*
  Expands e.g.
    +
  to
    λ x y. x + y

  *)

  Definition mk_var : nat -> string :=
    string_of_nat
  .

  From PlutusCert Require Import FreeVars.

  Definition fresh_var (t : term) : string :=
    concat "" (Term.fv t).

  Definition fresh_tyvar (t : term) : string :=
    concat "" (Term.ftv t).

  Fixpoint apps ( b : term) (args : list (term + ty)) : term :=
    match args with
      | [] => b
      | inl t :: xs => <{ {apps <{b ⋅ t}> xs} }>
      | inr T :: xs => <{ {apps <{b @ T}> xs} }>
    end
  .

  Fixpoint eta_expand_sig (s : builtin_sig) (f : DefaultFun) (args : list (term + ty)) (n : nat) : term :=
    match s with
    | BS_Fun T s      => <{ λ {mk_var n} :: T, {eta_expand_sig s f (args ++ [inl (Var (mk_var n))]) (S n)} }>
    | BS_Forall X K s => <{ Λ {mk_var n} :: K, {eta_expand_sig s f (args ++ [inr (Ty_Var X)]) (S n)} }>
    | BS_Result T     => apps (Builtin f) args
    end
  .

  Definition eta_expand (f : DefaultFun) := eta_expand_sig (to_sig f) f [] 0.

  Compute eta_expand IfThenElse.

End Eta.


Section ByteString.

  Local Open Scope Z_scope.

  Definition Z_to_byte (z : Z) : option byte :=
    if (0 <=? z) && (z <=? 255) then Byte.of_nat (Z.to_nat z) else None.


  Definition Z_to_nat (z : Z) : option nat :=
    if (0 <=? z) then Some (Z.to_nat z) else None
  .

  (*
  Returns an Error term if the integer is out of range (Semantic variant 2)
  *)
  Definition cons_bytestring (z : Z) (bs : list byte) : term :=
      match Z_to_byte z with
      | Some b => Constant (ValueOf DefaultUniByteString (b :: bs))
      | None   => Error (Ty_Builtin DefaultUniByteString)
      end
  .

  Local Open Scope list_scope.
  Definition slice_list {A} (s k : Z) (bs : list A) : list A :=
    let i := Z.max s 0 in
    let j := Z.min (s + k - 1) (Z.of_nat (List.length bs) - 1) in
    if j <? i
      then []
      else
        let len := (Z.to_nat j - Z.to_nat i + 1)%nat in
        firstn len (skipn (Z.to_nat i) bs)
  .

  Definition index_bytestring (bs : list byte) (c : Z) : term :=
    match Z_to_nat c with
      | Some n => match nth_error bs n with
        | Some b => <{ CInt {Z.of_nat (Byte.to_nat b)} }>
        | None => Error <{ ℤ }>
        end
      | None => Error <{ ℤ }>
      end
    .

  Axiom verify_Ed25519_signature : list byte -> list byte -> list byte -> bool.
  Axiom sha2_256 : list byte -> list byte.
  Axiom sha3_256 : list byte -> list byte.

End ByteString.


(*
Computes results of fully applied default functions where possible.
*)
Definition compute_defaultfun (t : term) : option term :=
  match t with
  (* Integer operations *)
  | <{ CInt n + CInt m }>  => Some <{ CInt {n + m} }>
  | <{ CInt n * CInt m }>  => Some <{ CInt {n * m} }>
  | <{ CInt n - CInt m }>  => Some <{ CInt {n - m} }>
  | <{ {Builtin DivideInteger} ⋅ CInt n ⋅ CInt m }> => Some <{ CInt {n / m} }>
  | <{ {Builtin QuotientInteger} ⋅ CInt n ⋅ CInt m }> => Some <{ CInt {n ÷ m} }>
  | <{ {Builtin RemainderInteger} }> => None
  | <{ {Builtin ModInteger} }> => None

  | <{ CInt n == CInt m }> => Some <{ CBool {n =? m} }>
  | <{ {Builtin LessThanInteger} }> => None
  | <{ {Builtin LessThanEqualsInteger} }> => None

  (* ByteString operations *)
  | <{ {Builtin AppendByteString } ⋅ CBS xs ⋅ CBS ys}> => Some <{ CBS {xs ++ ys} }>
  | <{ {Builtin ConsByteString } ⋅ CInt n ⋅ CBS xs}> => Some (cons_bytestring n xs)
  | <{ {Builtin SliceByteString } ⋅ CInt n ⋅ CInt m ⋅ CBS xs}> => Some <{ CBS {slice_list n m xs} }>
  | <{ {Builtin LengthOfByteString } ⋅ CBS xs}> => Some <{ CInt {Z.of_nat (List.length xs)} }>
  | <{ {Builtin IndexByteString } ⋅ CBS xs ⋅ CInt n}> => Some (index_bytestring xs n)
  | <{ {Builtin EqualsByteString} }> => None
  | <{ {Builtin LessThanByteString} }> => None
  | <{ {Builtin LessThanEqualsByteString} }> => None

  | <{ ifthenelse @ T ⋅ CBool b ⋅ s ⋅ t }> => Some (if b then s else t)

  (* Cryptography primitives *)
  | <{ {Builtin Sha2_256} ⋅ CBS bs }> => Some <{CBS {sha2_256 bs} }>
  | <{ {Builtin Sha3_256} ⋅ CBS bs }> => Some <{CBS {sha3_256 bs} }>
  | <{ {Builtin Blake2b_256} }> => None
  | <{ {Builtin VerifyEd25519Signature} ⋅ CBS xs ⋅ CBS ys ⋅ CBS zs}> => Some <{ CBool {verify_Ed25519_signature xs ys zs} }>
  | <{ {Builtin VerifyEcdsaSecp256k1Signature} }> => None
  | <{ {Builtin VerifySchnorrSecp256k1Signature} }> => None

  (* Strings *)
  | <{ {Builtin AppendString} }> => None
  | <{ {Builtin EqualsString} }> => None
  | <{ {Builtin EncodeUtf8} }> => None
  | <{ {Builtin DecodeUtf8} }> => None

  (* Unit *)
  | <{ {Builtin ChooseUnit} }> => None
  (* Tracing *)
  | <{ {Builtin Trace} }> => None
  (* Pairs *)
  | <{ {Builtin FstPair} }> => None
  | <{ {Builtin SndPair} }> => None
  (* Lists *)
  | <{ {Builtin ChooseList} }> => None
  | <{ {Builtin MkCons} }> => None
  | <{ {Builtin HeadList} }> => None
  | <{ {Builtin TailList} }> => None
  | <{ {Builtin NullList} }> => None
  (* Data *)
  | <{ {Builtin ChooseData} }> => None
  | <{ {Builtin ConstrData} }> => None
  | <{ {Builtin MapData} }> => None
  | <{ {Builtin ListData} }> => None
  | <{ {Builtin IData} }> => None
  | <{ {Builtin BData} }> => None
  | <{ {Builtin UnConstrData} }> => None
  | <{ {Builtin UnMapData} }> => None
  | <{ {Builtin UnListData} }> => None
  | <{ {Builtin UnIData} }> => None
  | <{ {Builtin UnBData} }> => None
  | <{ {Builtin EqualsData} }> => None
  | <{ {Builtin SerialiseData} }> => None
  (* Misc monomorphized constructors. *)
  | <{ {Builtin MkPairData} }> => None
  | <{ {Builtin MkNilData} }> => None
  | <{ {Builtin MkNilPairData} }> => None
  (* BLS12_381 operations *)
  (* G1 *)
  | <{ {Builtin Bls12_381_G1_add} }> => None
  | <{ {Builtin Bls12_381_G1_neg} }> => None
  | <{ {Builtin Bls12_381_G1_scalarMul} }> => None
  | <{ {Builtin Bls12_381_G1_equal} }> => None
  | <{ {Builtin Bls12_381_G1_hashToGroup} }> => None
  | <{ {Builtin Bls12_381_G1_compress} }> => None
  | <{ {Builtin Bls12_381_G1_uncompress} }> => None
  (* G2 *)
  | <{ {Builtin Bls12_381_G2_add} }> => None
  | <{ {Builtin Bls12_381_G2_neg} }> => None
  | <{ {Builtin Bls12_381_G2_scalarMul} }> => None
  | <{ {Builtin Bls12_381_G2_equal} }> => None
  | <{ {Builtin Bls12_381_G2_hashToGroup} }> => None
  | <{ {Builtin Bls12_381_G2_compress} }> => None
  | <{ {Builtin Bls12_381_G2_uncompress} }> => None
  (* Pairing *)
  | <{ {Builtin Bls12_381_millerLoop} }> => None
  | <{ {Builtin Bls12_381_mulMlResult} }> => None
  | <{ {Builtin Bls12_381_finalVerify} }> => None
  (* Keccak_256, Blake2b_224 *)
  | <{ {Builtin Keccak_256} }> => None
  | <{ {Builtin Blake2b_224} }> => None
  (* Conversions *)
  | <{ {Builtin IntegerToByteString} }> => None
  | <{ {Builtin ByteStringToInteger} }> => None

  | _ => None (* TODO*)
  end
.
