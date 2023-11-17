(* GHC Core *)
(*

  Very much incomplete port of

  https://hackage.haskell.org/package/ghc-8.10.1/docs/src/CoreSyn.html

*)
Require Import ZArith.BinInt.
Require Import Strings.String.
Local Open Scope Z_scope.

Inductive Char.
Definition LitNumType := unit.
Definition Integer := Z.
Definition TType := unit. (* Renamed from Type *)
Inductive ByteString.
Inductive Rational.
Inductive FastString.
Inductive Int.
Inductive Maybe (A : Set) : Set.
Inductive FunctionOrData.
Definition Id := string. (* simplified, see  https://hackage.haskell.org/package/ghc-8.10.1/docs/src/Var.html#Id *)
Inductive DataCon.
Inductive Coercion.
Inductive Tickish (A : Set) : Set.

Inductive Literal : Set :=
  | LitChar   : Char -> Literal
  | LitNumber : LitNumType -> Integer -> TType -> Literal
  | LitString : ByteString -> Literal
  | LitNullAddr
  | LitRubbish
  | LitFloat  : Rational -> Literal
  | LitDouble : Rational -> Literal
  | LitLabel  : FastString -> Maybe Int -> FunctionOrData -> Literal
.

Inductive AltCon :=
  | DataAlt : DataCon -> AltCon
  | LitAlt : Literal -> AltCon
  | DEFAULT
.

Set Implicit Arguments.
Set Contextual Implicit.
Inductive Expr (b : Set) : Set :=
  | Var       : Id -> Expr b
  | Lit       : Literal -> Expr b
  | App       : Expr b -> Expr b -> Expr b
  | Lam       : b -> Expr b -> Expr b
  | Let       : Bind b -> Expr b -> Expr b
  | Case      : Expr b -> b -> TType -> list (AltCon * list b * Expr b) -> Expr b
  | Cast      : Expr b -> Coercion -> Expr b
  | Tick      : Tickish Id -> Expr b -> Expr b
  | EType     : TType -> Expr b    (* Renamed from Type *)
  | ECoercion : Coercion -> Expr b (* Renamed from Coercion *)

with Bind (b : Set) : Set :=
  | NonRec : b -> Expr b -> Bind b
  | Rec    : list (b * Expr b) -> Bind b
.
