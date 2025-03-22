Require Import Coq.Strings.String.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import Util.
Set Implicit Arguments.

Require Import Coq.Program.Basics.

Import ListNotations.



From QuickChick Require Import QuickChick.
(*
  Simplification of the names in the AST

  In the AST that we dump in the plutus compiler, variables are represented with the Name type, which is
  a pair of String and Int, where the Int (newtyped as Unique) is used as a compiler detail for cheap name
  comparisons (see Language.PlutusCore.Name.

  We ignore these details and treat names (both terms and types) as strings. The definitions
  below have the same types as the original AST constructors, but forget the structure and
  map to a string.

  This simplifies the representation and especially recognizing equal subterms (since
  compiler passes may reassign unique numbers).

  Possible future approach: it is preferable to have to complete AST including e.g.
  Uniques, but prove that they do not matter for evaluation and then remove them from
  AST

*)

(** recursivity and strictness *)
Inductive recursivity := NonRec | Rec.

Inductive strictness := NonStrict | Strict.

(** Default universe

In the compiler implementation, this is a GADT: the constructors have an index
for their Haskell interpretation. This enforces that only well-kinded types can be constructed.
Since types may have different kinds (e.g. List vs Integer), the GADT is not directly
annotated with its type, but by its (Haskell) kind and its (Haskell) type. The (Haskell) kind
is not visible though, as it is existentially quantified. For example:

    -- Existential quantification of a kind.
    data Esc = forall k. Esc k

    data DefaultUni =
    ...
    | DefaultUniApply ::
       !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))

This approach makes that one can construct plutus types that are of higher kind, e.g.

  Ty_Builtin (SomeTypeIn DefaultUniList)

This is useful for polymorphic function types (see compiler Note [Representing polymorphism]).

For representing constants of builtin types (which can only have kind * ), the compiler has

  data ValueOf uni a = ValueOf !(uni (Esc a)) !a

Since the last argument a is inferred as kind *, the use of GADT for DefaultUniverse will
only construct values of plutus types with the right kind.

In our Coq encoding, we don't use indexed types, as Coq doesn't always have the same
conveniences for pattern matching, and automatisation such as deriving. Instead we can
have dependently typed functions that compute the right types for constructing values
(see uniType and Constant).
*)
Inductive DefaultUni : Type :=
    | DefaultUniInteger
    | DefaultUniByteString
    | DefaultUniString
    | DefaultUniUnit
    | DefaultUniBool
    | DefaultUniProtoList
    | DefaultUniProtoPair
    | DefaultUniData
    | DefaultUniBLS12_381_G1_Element
    | DefaultUniBLS12_381_G2_Element
    | DefaultUniBLS12_381_MlResult

    | DefaultUniApply : DefaultUni -> DefaultUni -> DefaultUni
    .

QCDerive EnumSized for DefaultUni.


Inductive Data :=
  | DataConstr : Z -> list Data -> Data
  | DataMap : list (Data * Data) -> Data
  | DataList : list Data -> Data
  | DataI : Z -> Data
  | DataB : string -> Data
  .

(** Coq interpretation of plutus built-in types of base kind. If not of
* base-kind (or not well-kinded), returns None.
*)
Fixpoint uniType_option (x : DefaultUni) : option Set :=
  match x with
    | DefaultUniInteger    => Some Z
    | DefaultUniByteString => Some (list byte)
    | DefaultUniString => Some (list byte) (* UTF-8 encoded strings *)
    | DefaultUniUnit => Some unit
    | DefaultUniData => Some Data
    | DefaultUniBLS12_381_G1_Element => Some Z
    | DefaultUniBLS12_381_G2_Element => Some Z
    | DefaultUniBLS12_381_MlResult => Some Z
    | DefaultUniBool => Some bool

    | DefaultUniApply DefaultUniProtoList t =>
      match uniType_option t with
        | None => None
        | Some A => Some (list A)
      end

    | DefaultUniApply (DefaultUniApply DefaultUniProtoPair s) t =>
      match uniType_option s, uniType_option t with
      | Some A, Some B => Some (prod A B)
      | _, _ => None
      end

    | DefaultUniApply _ _ => None
    | DefaultUniProtoList => None
    | DefaultUniProtoPair => None
  end
  .
Functional Scheme uniType_option_rect := Induction for uniType_option Sort Type.


(** Coq interpretation of plutus built-in types of base kind. Used for constructing
constants (See term.Constant). Types that are ill-kinded or do not have base kind are
mapped to the empty type, ensuring that Constants of such type can be constructed.
*)
Definition uniType (x : DefaultUni) : Type :=
  match uniType_option x with
    | None => Empty_set
    | Some ty => ty
  end.

(* Constants are coq values of the interpretation of some type in
   DefaultUni *)
Inductive constant :=
  ValueOf : forall (T : DefaultUni), uniType T -> constant.

(** Built-in functions*)
Inductive DefaultFun :=

    | AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | EqualsInteger
    | LessThanInteger
    | LessThanEqualsInteger
    (* Bytestrings *)
    | AppendByteString
    | ConsByteString
    | SliceByteString
    | LengthOfByteString
    | IndexByteString
    | EqualsByteString
    | LessThanByteString
    | LessThanEqualsByteString
    (* Cryptography and hashes *)
    | Sha2_256
    | Sha3_256
    | Blake2b_256
    | VerifyEd25519Signature  (* formerly verifySignature *)
    | VerifyEcdsaSecp256k1Signature
    | VerifySchnorrSecp256k1Signature
    (* Strings *)
    | AppendString
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    (* Bool *)
    | IfThenElse
    (* Unit *)
    | ChooseUnit
    (* Tracing *)
    | Trace
    (* Pairs *)
    | FstPair
    | SndPair
    (* Lists *)
    | ChooseList
    | MkCons
    | HeadList
    | TailList
    | NullList
    (* Data *)
    | ChooseData
    | ConstrData
    | MapData
    | ListData
    | IData
    | BData
    | UnConstrData
    | UnMapData
    | UnListData
    | UnIData
    | UnBData
    | EqualsData
    | SerialiseData
    (* Misc monomorphized constructors. *)
    | MkPairData
    | MkNilData
    | MkNilPairData
    (* BLS12_381 operations *)
    (* G1 *)
    | Bls12_381_G1_add
    | Bls12_381_G1_neg
    | Bls12_381_G1_scalarMul
    | Bls12_381_G1_equal
    | Bls12_381_G1_hashToGroup
    | Bls12_381_G1_compress
    | Bls12_381_G1_uncompress
    (* G2 *)
    | Bls12_381_G2_add
    | Bls12_381_G2_neg
    | Bls12_381_G2_scalarMul
    | Bls12_381_G2_equal
    | Bls12_381_G2_hashToGroup
    | Bls12_381_G2_compress
    | Bls12_381_G2_uncompress
    (* Pairing *)
    | Bls12_381_millerLoop
    | Bls12_381_mulMlResult
    | Bls12_381_finalVerify
    (* Keccak_256, Blake2b_224 *)
    | Keccak_256
    | Blake2b_224
    (* Conversions *)
    | IntegerToByteString
    | ByteStringToInteger
.

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

(** kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Ty_Var : tyname -> ty
  | Ty_Fun : ty -> ty -> ty
  | Ty_IFix : ty -> ty -> ty
  | Ty_Forall : binderTyname -> kind -> ty -> ty
  | Ty_Builtin : DefaultUni -> ty
  | Ty_Lam : binderTyname -> kind -> ty -> ty
  | Ty_App : ty -> ty -> ty
  | Ty_SOP : (list (list ty)) -> ty
.

From PlutusCert Require Import plutus_util.

Section ty__ind.
  Unset Implicit Arguments.

  (* Variable for the property to prove about `ty` *)
  Variable (P : ty -> Prop).

  (* Hypotheses for each constructor of `ty` *)
  Context
    (H_Var : forall (X : tyname), P (Ty_Var X))
    (H_Fun : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_Fun T1 T2))
    (H_IFix : forall (F T : ty), P F -> P T -> P (Ty_IFix F T))
    (H_Forall : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Forall X K T))
    (H_Builtin : forall (T : DefaultUni), P (Ty_Builtin T))
    (H_Lam : forall (X : binderTyname) (K : kind) (T : ty), P T -> P (Ty_Lam X K T))
    (H_App : forall (T1 T2 : ty), P T1 -> P T2 -> P (Ty_App T1 T2))
    (H_SOP : forall (Tss : list (list ty)), ForallP22 P Tss -> P (Ty_SOP Tss)).

  Definition tyss__ind (tys_rect : forall (ts : list ty), ForallP P ts) (ty_rect : forall (t : ty), P t) :=
    fix tyss_rect' (tss : list (list ty)) :=
    match tss as p return ForallP22 P p with
      | nil       => ForallP2_nil P
      | cons ts tss => ForallP2_cons P (tys_rect ts) (tyss_rect' tss)
    end.

  Definition tys__ind (ty_rect : forall (t : ty), P t) :=
    fix tys_rect (ts : list ty) : ForallP P ts :=
    match ts as p return ForallP P p with
      | nil       => ForallP_nil
      | cons t ts => ForallP_cons (ty_rect t) (tys_rect ts)
    end.

  (* Main induction principle for `ty` *)
  Fixpoint ty__ind (T : ty) : P T :=
    match T with
    | Ty_Var X => H_Var X
    | Ty_Fun T1 T2 => H_Fun T1 T2 (ty__ind T1) (ty__ind T2)
    | Ty_IFix F T => H_IFix F T (ty__ind F) (ty__ind T)
    | Ty_Forall X K T => H_Forall X K T (ty__ind T)
    | Ty_Builtin T => H_Builtin T
    | Ty_Lam X K T => H_Lam X K T (ty__ind T)
    | Ty_App T1 T2 => H_App T1 T2 (ty__ind T1) (ty__ind T2)
    | Ty_SOP Tss => H_SOP Tss (tyss__ind (tys__ind ty__ind) ty__ind Tss)
    end.

End ty__ind.