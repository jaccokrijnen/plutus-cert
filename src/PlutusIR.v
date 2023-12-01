Require Import Coq.Strings.String.
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

(** Recursivity and strictness *)
Inductive Recursivity := NonRec | Rec.

Inductive Strictness := NonStrict | Strict.

(** Universes *)
Inductive DefaultUni : Type :=
    | DefaultUniInteger
    | DefaultUniByteString
    | DefaultUniString
    | DefaultUniUnit
    | DefaultUniBool
    | DefaultUniProtoList
    | DefaultUniProtoPair
    | DefaultUniApply : DefaultUni -> DefaultUni -> DefaultUni
    | DefaultUniData
    | DefaultUniBLS12_381_G1_Element
    | DefaultUniBLS12_381_G2_Element
    | DefaultUniBLS12_381_MlResult
    .

QCDerive EnumSized for DefaultUni.

(** Existentials as a datype *)
Inductive some {f : DefaultUni -> Type} :=
  Some' : forall {u : DefaultUni}, f u -> some.
Arguments some _ : clear implicits.

(** Builtin types *)
Inductive typeIn (u : DefaultUni) :=
  TypeIn : typeIn u.
Arguments TypeIn _ : clear implicits.

Definition SomeTypeIn (ty : DefaultUni) := @Some' typeIn ty (TypeIn ty).


Inductive Data :=
  | DataConstr : Z -> list Data -> Data
  | DataMap : list (Data * Data) -> Data
  | DataList : list Data -> Data
  | DataI : Z -> Data
  | DataB : string -> Data
  .

(** Constants *)
Fixpoint uniType (x : DefaultUni) : Type :=
  match x with
    | DefaultUniInteger => Z
    | DefaultUniByteString => string
    | DefaultUniString => string
    | DefaultUniUnit => unit
    | DefaultUniBool => bool
    | DefaultUniData => Data

    | DefaultUniApply DefaultUniProtoList t => list (uniType t)
    | DefaultUniApply (DefaultUniApply DefaultUniPair t1) t2 => uniType t1 * uniType t2

    | DefaultUniApply _ _ => Empty_set
    | DefaultUniBLS12_381_G1_Element => Z
    | DefaultUniBLS12_381_G2_Element => Z
    | DefaultUniBLS12_381_MlResult => Empty_set
    | DefaultUniProtoList => Empty_set
    | DefaultUniProtoPair => Empty_set
  end.

Inductive valueOf (u : DefaultUni) :=
  ValueOf : uniType u -> valueOf u.
Arguments ValueOf _ _ : clear implicits.

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
.
Section AST_term.
Context (name tyname : Set).
Context (binderName binderTyname : Set).

(** Kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** Types *)
Inductive ty :=
  | Ty_Var : tyname -> ty
  | Ty_Fun : ty -> ty -> ty
  | Ty_IFix : ty -> ty -> ty
  | Ty_Forall : binderTyname -> kind -> ty -> ty
  | Ty_Builtin : @some typeIn -> ty
  | Ty_Lam : binderTyname -> kind -> ty -> ty
  | Ty_App : ty -> ty -> ty.

(*
  Simplification of attached values in the AST

  In the Haskell AST, Term is a functor and each constructor may have a field of the type parameter
  `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
  (this works because the dumping code is ignoring it)

  TODO: perhaps use a similar approach to the simplification of names, by ignoring the argument
  in each constructor (have to add types for the possible values that can occur when dumping)
*)

(** Declarations *)
Inductive vdecl := VarDecl : binderName -> ty -> vdecl.
Inductive tvdecl := TyVarDecl : binderTyname -> kind -> tvdecl.

(* This is a bit in-between hack of having types in the AST and completely ignoring them*)
(* Constructor name and arity, needed for Scott encoding *)
Inductive constr := Constructor : vdecl -> nat -> constr.
Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> binderName -> list vdecl -> dtdecl.

(** Terms and bindings *)
Inductive term :=
  | Let      : Recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : binderTyname -> kind -> term -> term
  | LamAbs   : binderName -> ty -> term -> term
  | Apply    : term -> term -> term
  | Constant : @some valueOf -> term
  | Builtin  : DefaultFun -> term
  | TyInst   : term -> ty -> term
  | Error    : ty -> term
  | IWrap    : ty -> ty -> term -> term
  | Unwrap   : term -> term
  | Constr   : nat -> list term -> term
  | Case     : term -> list term -> term

with binding :=
  | TermBind : Strictness -> vdecl -> term -> binding
  | TypeBind : tvdecl -> ty -> binding
  | DatatypeBind : dtdecl -> binding
.

Inductive context :=
  | C_Hole     : context

  | C_LamAbs   : binderName -> ty -> context -> context
  | C_Apply_L    : context -> term -> context
  | C_Apply_R    : term -> context -> context
  .

(* Similar to mkLet in Plutus: for an empty list of bindings it is the identity, otherwise
   it constructs a let with a non-empty list of bindings *)
Definition mk_let (r : Recursivity) (bs : list binding) (t : term) : term :=
  match bs with
    | [] => t
    | _  => Let r bs t
  end
.

Fixpoint context_apply (C : context) (t : term) :=
  match C with
    | C_Hole           => t
    | C_LamAbs bn ty C => LamAbs bn ty (context_apply C t)
    | C_Apply_L C t'   => Apply (context_apply C t) t'
    | C_Apply_R t' C   => Apply t' (context_apply C t)
  end
.

(** ** Trace of compilation *)
Inductive pass :=
  | PassRename
  | PassTypeCheck
  | PassInline : list name -> pass
  | PassDeadCode
  | PassThunkRec
  | PassFloatTerm
  | PassLetNonStrict
  | PassLetTypes
  | PassLetRec
  | PassLetNonRec.

Inductive compilation_trace :=
  | CompilationTrace : term -> list (pass * term) -> compilation_trace.

(* These constructors should treat the type parameter
   as implicit too

   Using maximally inserted implicits for ease of use with
   partial application *)

End AST_term.

Arguments Ty_Var {_ _}.
Arguments Ty_Fun {_ _}.
Arguments Ty_IFix {_ _}.
Arguments Ty_Forall {_ _}.
Arguments Ty_Builtin {_ _}.
Arguments Ty_Lam {_ _}.
Arguments Ty_App {_ _}.

Arguments Let {_ _ _ _}.
Arguments Var {_ _ _ _}.
Arguments TyAbs {_ _ _ _}.
Arguments LamAbs {_ _ _ _}.
Arguments Apply {_ _ _ _}.
Arguments Constant {_ _ _ _}.
Arguments Builtin {_ _ _ _}.
Arguments TyInst {_ _ _ _}.
Arguments Error {_ _ _ _}.
Arguments IWrap {_ _ _ _}.
Arguments Unwrap {_ _ _ _}.
Arguments Constr {_ _ _ _}.
Arguments Case {_ _ _ _}.

Arguments TermBind {_ _ _ _}.
Arguments TypeBind {_ _ _ _}.
Arguments DatatypeBind {_ _ _ _}.

Arguments VarDecl {_ _ _}.
Arguments TyVarDecl {_}.
Arguments Datatype {_ _ _}.

Arguments PassRename {_}%type_scope.
Arguments PassTypeCheck {_}%type_scope.
Arguments PassInline {_}%type_scope.
Arguments PassDeadCode {_}%type_scope.
Arguments PassThunkRec {_}%type_scope.
Arguments PassFloatTerm {_}%type_scope.
Arguments PassLetNonStrict {_}%type_scope.
Arguments PassLetTypes {_}%type_scope.
Arguments PassLetRec {_}%type_scope.
Arguments PassLetNonRec {_}%type_scope.

Arguments CompilationTrace {name tyname binderName binderTyname}.


Definition constructorName {tyname binderName binderTyname} : constr tyname binderName binderTyname -> binderName :=
  fun c => match c with
  | Constructor (VarDecl n _) _ => n
  end
  .

Definition constructorType {tyname binderName binderTyname} :
  constr tyname binderName binderTyname -> ty tyname binderTyname :=
  fun c => match c with
  | Constructor (VarDecl _ ty) _ => ty
  end
  .

Definition TyVarDeclVar {binderTyname} :
  tvdecl binderTyname -> binderTyname :=
    fun tvd =>
      match tvd with
      | TyVarDecl v ty => v
      end
.

(** * Named terms (all variables and binders are strings) *)
Module NamedTerm.

(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)


Definition Unique (n : nat) := n.
(*
Inductive unique := Unique : nat -> unique.
  Definition unique_dec : forall u u' : unique, {u = u'} + {u <> u'}.
  Proof. decide equality. apply Nat.eq_dec. Defined.
*)

Definition Name (s : string) (n : nat) := string_of_nat n.
(*
Inductive name := Name : string -> unique -> name.

Definition name_dec : forall n1 n2 : name, {n1 = n2} + {n1 <> n2}.
Proof. decide equality. apply unique_dec. apply string_dec. Defined.
*)

Definition TyName (s : string) := s.
(*
Inductive tyname := TyName : name -> tyname.
*)

Notation Kind := (kind).
Notation Ty := (ty string string).
Notation VDecl := (vdecl string string string).
Notation TVDecl := (tvdecl string).
Notation DTDecl := (dtdecl string string string).
Notation constructor := (constr string string string).
Notation Term := (term string string string string).
Notation Binding := (binding string string string string).

Notation Context := (context string string string string).

Arguments C_Hole { _ _ _ _ }.


Open Scope string_scope.
Definition Some := @Some'.
Arguments Some {_ _}.
Open Scope Z_scope.
Definition t := 
  Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySchnorrSecp256k1Signature") (Unique (34))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool))))))) (Builtin (VerifySchnorrSecp256k1Signature))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifyEd25519Signature") (Unique (35))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool))))))) (Builtin (VerifyEd25519Signature))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifyEcdsaSecp256k1Signature") (Unique (33))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool))))))) (Builtin (VerifyEcdsaSecp256k1Signature))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unsafeDataAsMap") (Unique (85))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))))) (Builtin (UnMapData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unsafeDataAsList") (Unique (86))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))))) (Builtin (UnListData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unsafeDataAsI") (Unique (88))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger))))) (Builtin (UnIData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unsafeDataAsConstr") (Unique (84))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))))) (Builtin (UnConstrData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unsafeDataAsB") (Unique (87))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (UnBData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("unitval") (Unique (15))) (Ty_Builtin (SomeTypeIn (DefaultUniUnit)))) (Constant (Some (ValueOf (DefaultUniUnit) (tt))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("true") (Unique (13))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))) (Constant (Some (ValueOf (DefaultUniBool) (true))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (55))) (Ty_Forall (TyName (Name ("a") (Unique (54)))) (Kind_Base) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (54))))) (Ty_Var (TyName (Name ("a") (Unique (54))))))))) (Builtin (Trace))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("tail") (Unique (68))) (Ty_Forall (TyName (Name ("a") (Unique (67)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (67)))))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (67))))))))) (Builtin (TailList))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (37))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("snd") (Unique (61))) (Ty_Forall (TyName (Name ("a") (Unique (59)))) (Kind_Base) (Ty_Forall (TyName (Name ("b") (Unique (60)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Var (TyName (Name ("a") (Unique (59)))))) (Ty_Var (TyName (Name ("b") (Unique (60)))))) (Ty_Var (TyName (Name ("b") (Unique (60))))))))) (Builtin (SndPair))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sliceByteString") (Unique (20))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))))) (Builtin (SliceByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (24))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Sha3_256))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (23))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Sha2_256))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("serialiseData") (Unique (89))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (SerialiseData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (42))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (41))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("null") (Unique (64))) (Ty_Forall (TyName (Name ("a") (Unique (63)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (63)))))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (NullList))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (38))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (40))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkPairData") (Unique (62))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))))) (Builtin (MkPairData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkNilPairData") (Unique (73))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniUnit))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))))) (Builtin (MkNilPairData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkNilData") (Unique (72))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniUnit))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))))) (Builtin (MkNilData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkMap") (Unique (80))) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))) (Builtin (MapData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkList") (Unique (81))) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))) (Builtin (ListData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkI") (Unique (82))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))) (Builtin (IData))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinData") (Unique (5)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (nil)) (Let (Rec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (113)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (114))) (cons (VarDecl (Name ("Unit") (Unique (115))) (Ty_Var (TyName (Name ("Unit") (Unique (113)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("mkGiftValidator") (Unique (116))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Var (TyName (Name ("Unit") (Unique (113))))))))) (LamAbs (Name ("ds") (Unique (117))) (Ty_Builtin (SomeTypeIn (DefaultUniData))) (LamAbs (Name ("ds") (Unique (118))) (Ty_Builtin (SomeTypeIn (DefaultUniData))) (LamAbs (Name ("ds") (Unique (119))) (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Var (Name ("Unit") (Unique (115)))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkConstr") (Unique (79))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))) (Ty_Builtin (SomeTypeIn (DefaultUniData)))))) (Builtin (ConstrData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkCons") (Unique (75))) (Ty_Forall (TyName (Name ("a") (Unique (74)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (74))))) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (74)))))) (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (74)))))))))) (Builtin (MkCons))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("mkB") (Unique (83))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniData))))) (Builtin (BData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (43))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (LessThanInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqualsInteger") (Unique (44))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (LessThanEqualsInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqualsByteString") (Unique (30))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (LessThanEqualsByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (29))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (LessThanByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lengthOfByteString") (Unique (21))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger))))) (Builtin (LengthOfByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("keccak_") (Unique (27))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Keccak_256))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("integerNegate") (Unique (111))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger))))) (LamAbs (Name ("x") (Unique (112))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Apply (Apply (Builtin (SubtractInteger)) (Constant (Some (ValueOf (DefaultUniInteger) (0))))) (Var (Name ("x") (Unique (112))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("indexByteString") (Unique (22))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (IndexByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("ifThenElse") (Unique (12))) (Ty_Forall (TyName (Name ("a") (Unique (11)))) (Kind_Base) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBool))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (11))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (11))))) (Ty_Var (TyName (Name ("a") (Unique (11)))))))))) (Builtin (IfThenElse))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("head") (Unique (66))) (Ty_Forall (TyName (Name ("a") (Unique (65)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (65)))))) (Ty_Var (TyName (Name ("a") (Unique (65)))))))) (Builtin (HeadList))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("fst") (Unique (58))) (Ty_Forall (TyName (Name ("a") (Unique (56)))) (Kind_Base) (Ty_Forall (TyName (Name ("b") (Unique (57)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair))) (Ty_Var (TyName (Name ("a") (Unique (56)))))) (Ty_Var (TyName (Name ("b") (Unique (57)))))) (Ty_Var (TyName (Name ("a") (Unique (56))))))))) (Builtin (FstPair))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("false") (Unique (14))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))) (Constant (Some (ValueOf (DefaultUniBool) (false))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (49))) (Ty_Forall (TyName (Name ("a") (Unique (48)))) (Kind_Base) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniUnit))) (Ty_Var (TyName (Name ("a") (Unique (48)))))))) (TyAbs (TyName (Name ("a") (Unique (46)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (47))) (Ty_Builtin (SomeTypeIn (DefaultUniUnit))) (Error (Ty_Var (TyName (Name ("a") (Unique (46))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsString") (Unique (52))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (EqualsString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (45))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (EqualsInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsData") (Unique (78))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (EqualsData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (28))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (EqualsByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("encodeUtf") (Unique (53))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (EncodeUtf8))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (51))) (Ty_Builtin (SomeTypeIn (DefaultUniString)))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (31))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString)))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (39))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("decodeUtf") (Unique (32))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniString))))) (Builtin (DecodeUtf8))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("consByteString") (Unique (19))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString)))))) (Builtin (ConsByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("chooseUnit") (Unique (17))) (Ty_Forall (TyName (Name ("a") (Unique (16)))) (Kind_Base) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniUnit))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (16))))) (Ty_Var (TyName (Name ("a") (Unique (16))))))))) (Builtin (ChooseUnit))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("chooseList") (Unique (71))) (Ty_Forall (TyName (Name ("a") (Unique (69)))) (Kind_Base) (Ty_Forall (TyName (Name ("b") (Unique (70)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Builtin (SomeTypeIn (DefaultUniProtoList))) (Ty_Var (TyName (Name ("a") (Unique (69)))))) (Ty_Fun (Ty_Var (TyName (Name ("b") (Unique (70))))) (Ty_Fun (Ty_Var (TyName (Name ("b") (Unique (70))))) (Ty_Var (TyName (Name ("b") (Unique (70))))))))))) (Builtin (ChooseList))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("chooseData") (Unique (77))) (Ty_Forall (TyName (Name ("a") (Unique (76)))) (Kind_Base) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniData))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (76))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (76))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (76))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (76))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (76))))) (Ty_Var (TyName (Name ("a") (Unique (76))))))))))))) (Builtin (ChooseData))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_mulMlResult") (Unique (109))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult)))))) (Builtin (Bls12_381_mulMlResult))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_millerLoop") (Unique (108))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult)))))) (Builtin (Bls12_381_millerLoop))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_finalVerify") (Unique (110))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (Bls12_381_finalVerify))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_zero") (Unique (106))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))) (Constant (Some (ValueOf (DefaultUniBLS12_381_G2_Element) (0xc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_uncompress") (Unique (104))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))))) (Builtin (Bls12_381_G2_uncompress))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_scalarMul") (Unique (101))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))))) (Builtin (Bls12_381_G2_scalarMul))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_neg") (Unique (102))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))))) (Builtin (Bls12_381_G2_neg))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_hashToGroup") (Unique (105))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))))) (Builtin (Bls12_381_G2_hashToGroup))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_generator") (Unique (107))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))) (Constant (Some (ValueOf (DefaultUniBLS12_381_G2_Element) (0x93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_equals") (Unique (99))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (Bls12_381_G2_equal))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_compress") (Unique (103))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Bls12_381_G2_compress))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G2_add") (Unique (100))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))))) (Builtin (Bls12_381_G2_add))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_zero") (Unique (97))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))) (Constant (Some (ValueOf (DefaultUniBLS12_381_G1_Element) (0xc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_uncompress") (Unique (95))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))))) (Builtin (Bls12_381_G1_uncompress))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_scalarMul") (Unique (93))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))))) (Builtin (Bls12_381_G1_scalarMul))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_neg") (Unique (92))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))))) (Builtin (Bls12_381_G1_neg))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_hashToGroup") (Unique (96))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))))) (Builtin (Bls12_381_G1_hashToGroup))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_generator") (Unique (98))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))) (Constant (Some (ValueOf (DefaultUniBLS12_381_G1_Element) (0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_equals") (Unique (90))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))))) (Builtin (Bls12_381_G1_equal))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_compress") (Unique (94))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Bls12_381_G1_compress))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("bls12_381_G1_add") (Unique (91))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element))) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))))) (Builtin (Bls12_381_G1_add))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("blake2b_") (Unique (26))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Blake2b_256))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("blake2b_") (Unique (25))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString))))) (Builtin (Blake2b_224))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (50))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniString))) (Ty_Builtin (SomeTypeIn (DefaultUniString)))))) (Builtin (AppendString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendByteString") (Unique (18))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniByteString))) (Ty_Builtin (SomeTypeIn (DefaultUniByteString)))))) (Builtin (AppendByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (36))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Fun (Ty_Builtin (SomeTypeIn (DefaultUniInteger))) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (1)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniInteger)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinUnit") (Unique (3)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniUnit)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinString") (Unique (4)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniString)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinPair") (Unique (6)))) (Kind_Arrow (Kind_Base) (Kind_Arrow (Kind_Base) (Kind_Base)))) (Ty_Builtin (SomeTypeIn (DefaultUniProtoPair)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinList") (Unique (7)))) (Kind_Arrow (Kind_Base) (Kind_Base))) (Ty_Builtin (SomeTypeIn (DefaultUniProtoList)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinByteString") (Unique (0)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniByteString)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinBool") (Unique (2)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniBool)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinBLS12_381_MlResult") (Unique (10)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_MlResult)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinBLS12_381_G2_Element") (Unique (9)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G2_Element)))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("BuiltinBLS12_381_G1_Element") (Unique (8)))) (Kind_Base)) (Ty_Builtin (SomeTypeIn (DefaultUniBLS12_381_G1_Element)))) (nil)) (Var (Name ("mkGiftValidator") (Unique (116))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
.

End NamedTerm.



(** * De Bruijn terms *)
Module DeBruijnTerm.

Notation Kind := (kind).
Notation Ty := (ty nat unit).
Notation VDecl := (vdecl nat unit unit).
Notation TVDecl := (tvdecl unit).
Notation DTDecl := (dtdecl nat unit unit).
Notation constructor := (constr nat unit unit).
Notation Term := (term nat nat unit unit).
Notation Binding := (binding nat nat unit unit).


Fixpoint shift_ty' (k c : nat) (T : Ty) : Ty :=
  match T with
  | Ty_Var X => if X <? c then Ty_Var X else Ty_Var (k + X)
  | Ty_Fun T1 T2 => Ty_Fun (shift_ty' k c T1) (shift_ty' k c T2)
  | Ty_IFix F T0 => Ty_IFix (shift_ty' k c F) (shift_ty' k c T0)
  | Ty_Forall bX K T => Ty_Forall bX K (shift_ty' k (S c) T)
  | Ty_Builtin u => Ty_Builtin u
  | Ty_Lam bX K1 T => Ty_Lam bX K1 (shift_ty' k (S c) T)
  | Ty_App T1 T2 => Ty_App (shift_ty' k c T1) (shift_ty' k c T2)
  end.

Definition shift_ty (T : Ty) := shift_ty' 1 0 T.

(*
Equations shift_term' : nat -> nat -> Term -> Term := {
  shift_term' k c (Let NonRec bs t0) => Let NonRec (shift_bindings' k c bs) (shift_term' k (length bs + c) t0) ;
  shift_term' k c (Let Rec bs t0) => Let Rec (shift_bindings' k (length bs + c) bs (* TODO: shift by c or more? *)) (shift_term' k (length bs + c) t0) ;
  shift_term' k c (Var x) => if x <? c then Var x else Var (k + x) ;
  shift_term' k c (TyAbs bX K t0) => TyAbs bX K (shift_term' k (S c) t0) ;
  shift_term' k c (LamAbs bx T t0) => LamAbs bx (shift_ty' k c T) (shift_term' k (S c) t0) ;
  shift_term' k c (Apply t1 t2) => Apply (shift_term' k c t1) (shift_term' k c t2) ;
  shift_term' k c (Constant u) => Constant u ;
  shift_term' k c (Builtin d) => Builtin d ;
  shift_term' k c (TyInst t0 T) => TyInst (shift_term' k c t0) (shift_ty' k c T) ;
  shift_term' k c (Error T) => Error (shift_ty' k c T) ;
  shift_term' k c (IWrap F T t0) => IWrap (shift_ty' k c F) (shift_ty' k c T) (shift_term' k c t0) ;
  shift_term' k c (Unwrap t0) => Unwrap (shift_term' k c t0) }

where shift_bindings' : nat -> nat -> list Binding -> list Binding := {
  shift_bindings' k c nil => nil ;
  shift_bindings' k c (TermBind s (VarDecl bn T) t :: bs) => TermBind s (VarDecl bn (shift_ty' k c T)) (shift_term' k c t) :: shift_bindings' k c bs ;
  shift_bindings' k c (TypeBind tvd T :: bs) => TypeBind tvd (shift_ty' k c T) :: shift_bindings' k c bs ;
  shift_bindings' k c (DatatypeBind (Datatype X YKs matchFunc cs) :: bs) => DatatypeBind (Datatype X YKs matchFunc (shift_constructors' k c cs)) :: shift_bindings' k c bs}

where shift_constructors' : nat -> nat -> list constructor -> list constructor := {
  shift_constructors' k c nil => nil ;
  shift_constructors' k c (Constructor (VarDecl bn T) ar :: cs) => Constructor (VarDecl bn (shift_ty' k c T)) ar :: shift_constructors' k c cs }.

Definition shift_term (t : Term) := shift_term' 1 0 t.
*)

End DeBruijnTerm.


Module UniqueTerm.


Open Scope type_scope.
Definition name         := string * Z.
Definition tyname       := string * Z.
Definition binderName   := string * Z.
Definition binderTyname := string * Z.


Notation Kind := (kind).
Notation Ty := (ty tyname binderTyname).
Notation VDecl := (vdecl name tyname binderName).
Notation TVDecl := (tvdecl binderTyname).
Notation DTDecl := (dtdecl name tyname binderTyname).
Notation constructor := (constr tyname binderName binderTyname).
Notation Term := (term name tyname binderName binderTyname).
Notation Binding := (binding name tyname binderName binderTyname).


Definition Name x y : string * Z := (x, y).
Definition Unique x : Z := x.
Definition TyName name : string * Z := name.


End UniqueTerm.


Section Term_rect.
  Import NamedTerm.

  Unset Implicit Arguments.

  Variable (P : Term -> Type).
  Variable (Q : Binding -> Type).

  Context
    (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : string, P (Var s))
    (H_TyAbs    : forall (s : string) (k : Kind) (t : Term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : string) (t : Ty) (t0 : Term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : Term, P t -> forall t0 : Term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : Term, P t -> forall t0 : Ty, P (TyInst t t0))
    (H_Error    : forall t : Ty, P (Error t))
    (H_IWrap    : forall (t t0 : Ty) (t1 : Term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : Term, P t -> P (Unwrap t))
    (H_Constr   : forall (i : nat) (ts : list Term), ForallT P ts -> P (Constr i ts))
    (H_Case     : forall (t : Term), P t -> forall ts, ForallT P ts -> P (Case t ts))
    .

  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition Bindings_rect' (Binding_rect' : forall (b : Binding), Q b) :=
    fix Bindings_rect' bs :=
    match bs as p return ForallT Q p with
      | nil       => ForallT_nil
      | cons b bs => ForallT_cons (Binding_rect' b) (Bindings_rect' bs)
    end.

  Definition Terms_rect' (Term_rect : forall (t : Term), P t) :=
    fix Terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (Term_rect t) (Terms_rect' ts)
    end.

  Fixpoint Term_rect' (t : Term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (Bindings_rect' Binding_rect' bs) (Term_rect' t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (Term_rect' t)
      | LamAbs n ty t   => H_LamAbs n ty t (Term_rect' t)
      | Apply s t       => H_Apply s (Term_rect' s) t (Term_rect' t)
      | TyInst t ty     => H_TyInst t (Term_rect' t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (Term_rect' t)
      | Unwrap t        => H_Unwrap t (Term_rect' t)
      | Error ty        => H_Error ty
      | Constant v      => H_Constant v
      | Builtin f       => H_Builtin f
      | Constr i ts     => H_Constr i ts (Terms_rect' Term_rect' ts)
      | Case t ts       => H_Case t (Term_rect' t) ts (Terms_rect' Term_rect' ts)
    end
  with Binding_rect' (b : Binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (Term_rect' t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.
End Term_rect.

Section Term__ind.
  Import NamedTerm.

  Unset Implicit Arguments.

  Variable (P : Term -> Prop).
  Variable (Q : Binding -> Prop).

  Context
    (H_Let      : forall rec bs t, ForallP Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : string, P (Var s))
    (H_TyAbs    : forall (s : string) (k : Kind) (t : Term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : string) (t : Ty) (t0 : Term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : Term, P t -> forall t0 : Term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : Term, P t -> forall t0 : Ty, P (TyInst t t0))
    (H_Error    : forall t : Ty, P (Error t))
    (H_IWrap    : forall (t t0 : Ty) (t1 : Term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : Term, P t -> P (Unwrap t))
    (H_Constr   : forall (i : nat) (ts : list Term), ForallP P ts -> P (Constr i ts))
    (H_Case    : forall (t : Term), P t -> forall ts, ForallP P ts -> P (Case t ts))
    .



  Context
    (H_TermBind : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Definition Bindings__ind (Binding__ind : forall (b : Binding), Q b) :=
    fix Bindings__ind bs :=
    match bs as p return ForallP Q p with
      | nil       => ForallP_nil
      | cons b bs => ForallP_cons (Binding__ind b) (Bindings__ind bs)
    end.

  Definition Terms__ind (Term_rect : forall (t : Term), P t) :=
    fix Terms_rect' ts :=
    match ts as p return ForallP P p with
      | nil       => ForallP_nil
      | cons t ts => ForallP_cons (Term_rect t) (Terms_rect' ts)
    end.

  Fixpoint Term__ind (t : Term) : P t :=
    match t with
      | Let rec bs t    => H_Let rec bs t (Bindings__ind Binding__ind bs) (Term__ind t)
      | Var n           => H_Var n
      | TyAbs n k t     => H_TyAbs n k t (Term__ind t)
      | LamAbs n ty t   => H_LamAbs n ty t (Term__ind t)
      | Apply s t       => H_Apply s (Term__ind s) t (Term__ind t)
      | TyInst t ty     => H_TyInst t (Term__ind t) ty
      | IWrap ty1 ty2 t => H_IWrap ty1 ty2 t (Term__ind t)
      | Unwrap t        => H_Unwrap t (Term__ind t)
      | Error ty        => H_Error ty
      | Constant v      => H_Constant v
      | Builtin f       => H_Builtin f
      | Constr i ts     => H_Constr i ts (Terms__ind Term__ind ts)
      | Case t ts      => H_Case t (Term__ind t) ts (Terms__ind Term__ind ts)
    end
  with Binding__ind (b : Binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (Term__ind t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme Term__multind from Term__ind, Binding__ind.

End Term__ind.

Section term_rect.
  Variable (v v' b b': Set).
  Variable (P : term v v' b b' -> Type).
  Variable (Q : binding v v' b b' -> Type).
  Variable (R : list (binding v v' b b') -> Type).

  Context
    (* (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_Let      : forall rec bs t, R bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : v, P (Var s))
    (H_TyAbs    : forall (s : b') (k : kind) (t : term v v' b b'), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : b) (t : ty v' b') (t0 : term v v' b b'), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : term v v' b b', P t -> forall t0 : term v v' b b', P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : term v v' b b', P t -> forall t0 : ty v' b', P (TyInst t t0))
    (H_Error    : forall t : ty v' b', P (Error t))
    (H_IWrap    : forall (t t0 : ty v' b') (t1 : term v v' b b'), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : term v v' b b', P t -> P (Unwrap t))
    (H_Constr   : forall (i : nat) (ts : list (term v v' b b')), ForallT P ts -> P (Constr i ts))
    (H_Case    : forall t, P t -> forall ts, ForallT P ts -> P (Case t ts)).

  Context
    (H_TermBind     : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind     : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons         : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil          : R nil).

  Definition bindings_rect' (binding_rect' : forall (b : binding v v' b b'), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Definition terms_rect' (term_rect : forall (t : term v v' b b'), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect' (t : term v v' b b') : P t :=
    match t with
      | Let rec bs t    => @H_Let rec bs t (bindings_rect' binding_rect' bs) (term_rect' t)
      | Var n           => @H_Var n
      | TyAbs n k t     => @H_TyAbs n k t (term_rect' t)
      | LamAbs n ty t   => @H_LamAbs n ty t (term_rect' t)
      | Apply s t       => @H_Apply s (term_rect' s) t (term_rect' t)
      | TyInst t ty     => @H_TyInst t (term_rect' t) ty
      | IWrap ty1 ty2 t => @H_IWrap ty1 ty2 t (term_rect' t)
      | Unwrap t        => @H_Unwrap t (term_rect' t)
      | Error ty        => @H_Error ty
      | Constant v      => @H_Constant v
      | Builtin f       => @H_Builtin f
      | Constr i ts     => @H_Constr i ts (terms_rect' term_rect' ts)
      | Case t ts      => @H_Case t (term_rect' t) ts (terms_rect' term_rect' ts)
    end
  with binding_rect' (b : binding v v' b b') : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

Section ty_fold.

  Context
    {V : Set}
    {B : Set}.
  Context
    {R : Set}.

  Context
    (f_Var : V -> R)
    (f_Fun : R -> R -> R)
    (f_IFix : R -> R -> R)
    (f_Forall : B -> kind -> R -> R)
    (f_Builtin : @some typeIn -> R)
    (f_Lam : B -> kind -> R -> R)
    (f_App : R -> R -> R).

  Definition ty_fold := fix f ty :=
    match ty with
    | Ty_Var v        => f_Var v
    | Ty_Fun t1 t2    => f_Fun (f t1) (f t2)
    | Ty_IFix t1 t2   => f_IFix (f t1) (f t2)
    | Ty_Forall v k t => f_Forall v k (f t)
    | Ty_Builtin b    => f_Builtin b
    | Ty_Lam v k t    => f_Lam v k (f t)
    | Ty_App t1 t2    => f_App (f t1) (f t2)
    end.

  Definition ty_alg (ty : ty V B) : Set := match ty with
    | Ty_Var v        => V -> R
    | Ty_Fun t1 t2    => R -> R -> R
    | Ty_IFix t1 t2   => R -> R -> R
    | Ty_Forall v k t => B -> kind -> R -> R
    | Ty_Builtin b    => @some typeIn -> R
    | Ty_Lam v k t    => B -> kind -> R -> R
    | Ty_App t1 t2    => R -> R -> R
    end.

End ty_fold.

Definition ty_endo {V B} (m_custom : forall τ, option (@ty_alg V B (ty V B) τ)) := fix f τ :=
  match m_custom τ with
    | Some f_custom => match τ return ty_alg τ -> ty V B with
      | Ty_Var v        => fun f_custom => f_custom v
      | Ty_Fun t1 t2    => fun f_custom => f_custom (f t1) (f t2)
      | Ty_IFix t1 t2   => fun f_custom => f_custom (f t1) (f t2)
      | Ty_Forall v k t => fun f_custom => f_custom v k (f t)
      | Ty_Builtin b    => fun f_custom => f_custom b
      | Ty_Lam v k t    => fun f_custom => f_custom v k (f t)
      | Ty_App t1 t2    => fun f_custom => f_custom (f t1) (f t2)
    end f_custom
    | None =>
      match τ with
      | Ty_Var v        => Ty_Var v
      | Ty_Fun t1 t2    => Ty_Fun (f t1) (f t2)
      | Ty_IFix t1 t2   => Ty_IFix (f t1) (f t2)
      | Ty_Forall v k t => Ty_Forall v k (f t)
      | Ty_Builtin b    => Ty_Builtin b
      | Ty_Lam v k t    => Ty_Lam v k (f t)
      | Ty_App t1 t2    => Ty_App (f t1) (f t2)
      end
  end.


(*
Inductive TermF termR bindingR :=
  | Let      : Recursivity -> list bindingR -> termR -> TermF
  | Var      : name -> TermF
  | TyAbs    : tyname -> Kind -> termR -> TermF
  | LamAbs   : name -> Ty -> termR -> TermF
  | Apply    : termR -> termR -> TermF
  | Constant : some -> TermF
  | Builtin  : func -> TermF
  | TyInst   : termR -> Ty -> TermF
  | Error    : Ty -> TermF
  | IWrap    : Ty -> Ty -> termR -> TermF
  | Unwrap   : termR -> TermF

with Binding termR bindingR :=
  | TermFBind    : Strictness -> VDecl -> termR -> Binding
  | TypeBind     : TVDecl -> Ty -> Binding
  | DatatypeBind : DTDecl -> Binding
.
Definition Mu (f : Type -> Type) (g : Type -> Type) := forall a, (f a -> a) -> (g a -> a) -> a.
*)

Definition unitVal : NamedTerm.Term := Constant (Some' (ValueOf DefaultUniUnit tt)).

Declare Scope plutus_scope.

Declare Custom Entry plutus_term.
Declare Custom Entry plutus_ty.
Declare Custom Entry plutus_kind.

Module PlutusNotations.

Notation "<{ e }>" := e (e custom plutus_term at level 99) : plutus_scope.
Notation "<{{ e }}>" := e (e custom plutus_ty at level 99) : plutus_scope.
Notation "<{{{ e }}}>" := e (e custom plutus_kind at level 99) : plutus_scope.
Notation "( x )" := x (in custom plutus_term, x at level 99) : plutus_scope.
Notation "( x )" := x (in custom plutus_ty, x at level 99) : plutus_scope.
Notation "( x )" := x (in custom plutus_kind, x at level 99) : plutus_scope.
Notation "x" := x (in custom plutus_term at level 0, x constr at level 0) : plutus_scope.
Notation "x" := x (in custom plutus_ty at level 0, x constr at level 0) : plutus_scope.
Notation "x" := x (in custom plutus_kind at level 0, x constr at level 0) : plutus_scope.
Notation "{ x }" := x (in custom plutus_term at level 1, x constr) : plutus_scope.
Notation "{ x }" := x (in custom plutus_ty at level 1, x constr) : plutus_scope.
Notation "{ x }" := x (in custom plutus_kind at level 1, x constr) : plutus_scope.

#[global]
Open Scope plutus_scope.
End PlutusNotations.
