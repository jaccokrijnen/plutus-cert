Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.BoolEq.
Require Import Ascii.
Require Import Eqdep.

From PlutusCert Require Import Util.
Set Implicit Arguments.

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

Definition Unique (n : nat) := tt.
(*
Inductive unique := Unique : nat -> unique.
  Definition unique_dec : forall u u' : unique, {u = u'} + {u <> u'}.
  Proof. decide equality. apply Nat.eq_dec. Defined.
*)

Definition Name (s : string) (n : unit) := s.
(*
Inductive name := Name : string -> unique -> name.

Definition name_dec : forall n1 n2 : name, {n1 = n2} + {n1 <> n2}.
Proof. decide equality. apply unique_dec. apply string_dec. Defined.
*)

Definition TyName (s : string) := s.
(*
Inductive tyname := TyName : name -> tyname.
*)


(*
  Simplification of types and kinds in the AST

  We also ignore kinds and types, and represent them with the unit type.

  TODO: take the same approach as with names (above). The dumping code in Haskell is ugly and prints
  units for types and kinds.
*)
Definition Kind := unit.
Definition Ty   := unit.

Inductive Recursivity := NonRec | Rec.

Inductive Strictness := NonStrict | Strict.


Inductive DefaultUni : Type :=
    | DefaultUniInteger    (* : DefaultUni nat (* Integer *) *)
    | DefaultUniByteString (* : DefaultUni string (* BS.ByteString *)*)
    | DefaultUniString     (* : DefaultUni string (* String *)*)
    | DefaultUniChar       (* : DefaultUni ascii (* Char *)*)
    | DefaultUniUnit       (* : DefaultUni unit (* () *)*)
    | DefaultUniBool       (* : DefaultUni bool (* Bool *)*)
    .
Definition uniType (x : DefaultUni) : Type :=
  match x with
    | DefaultUniInteger    => nat
    | DefaultUniByteString => string
    | DefaultUniString     => string
    | DefaultUniChar       => ascii
    | DefaultUniUnit       => unit
    | DefaultUniBool       => bool
  end
  .

Inductive DefaultFun :=
    | AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | LessThanInteger
    | LessThanEqInteger
    | GreaterThanInteger
    | GreaterThanEqInteger
    | EqInteger
    | Concatenate
    | TakeByteString
    | DropByteString
    | SHA2
    | SHA3
    | VerifySignature
    | EqByteString
    | LtByteString
    | GtByteString
    | IfThenElse
    | CharToString
    | Append
    | Trace.

Set Implicit Arguments.


(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)

(* TODO: Coq prints wrong notation for LamAbs type, perhaps just use string
    everywhere? *)
Notation name := string.
Notation tyname := string.
Notation uni := DefaultUni.
Notation func := DefaultFun.

Inductive valueOf (u : uni) :=
  ValueOf : uniType u -> valueOf u.
Arguments ValueOf _ _ : clear implicits.

(* Inductive valueOf a :=
  ValueOf : uni a -> a -> valueOf a.
Arguments ValueOf {_} {_}.
*)

Inductive some :=
  Some : forall {u : uni}, valueOf u -> some.
(*Inductive some := Some : forall a, valueOf a -> some.*)


(*
  Simplification of attached values in the AST

  In the Haskell AST, Term is a functor and each constructor may have a field of the type parameter
  `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
  (this works because the dumping code is ignoring it)

  TODO: perhaps use a similar approach to the simplification of names, by ignoring the argument
  in each constructor (have to add types for the possible values that can occur when dumping)
*)
Definition VDecl := string.
Definition VarDecl (x : name) (t : Ty) : VDecl := x.

(*
Inductive VDecl := VarDecl : name -> Ty -> VDecl.
*)

Inductive TVDecl := TyVarDecl : tyname -> Kind -> TVDecl.

(* Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list VDecl -> DTDecl.*)

(* This is a bit in-between hack of having types in the AST and completely ignoring them*)
(* Constructor name and arity, needed for Scott encoding *)
Inductive constructor :=
  | Constructor : string -> nat -> constructor.

Definition constructorName : constructor -> string := fun c => match c with
  | Constructor name _ => name
  end
  .

Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list constructor -> DTDecl.


Section AST_term.
Context (name : Set).

Inductive term :=
  | Let      : Recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : tyname -> Kind -> term -> term
  | LamAbs   : name -> Ty -> term -> term
  | Apply    : term -> term -> term
  | Constant : some -> term
  | Builtin  : func -> term
  | TyInst   : term -> Ty -> term
  | Error    : Ty -> term
  | IWrap    : Ty -> Ty -> term -> term
  | Unwrap   : term -> term

with binding :=
  | TermBind : Strictness -> name -> term -> binding
  | TypeBind : TVDecl -> Ty -> binding
  | DatatypeBind : DTDecl -> binding
.


End AST_term.

(* These constructors should treat the type parameter
   as implicit too (this is already correctly generated for the recursive
   constructors. *)

Arguments Constant [name]%type_scope.
Arguments Builtin [name]%type_scope.
Arguments Error [name]%type_scope.
Arguments TypeBind [name]%type_scope.
Arguments DatatypeBind [name]%type_scope.

Notation Term := (term string).
Notation Binding := (binding string).


Section Term_rect.
  Unset Implicit Arguments.

  Variable (P : Term -> Type).
  Variable (Q : Binding -> Type).

  Context
    (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : tyname, P (Var s))
    (H_TyAbs    : forall (s : tyname) (k : Kind) (t : Term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : tyname) (t : Ty) (t0 : Term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : Term, P t -> forall t0 : Term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some, P (Constant s))
    (H_Builtin  : forall d : func, P (Builtin d))
    (H_TyInst   : forall t : Term, P t -> forall t0 : Ty, P (TyInst t t0))
    (H_Error    : forall t : Ty, P (Error t))
    (H_IWrap    : forall (t t0 : Ty) (t1 : Term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : Term, P t -> P (Unwrap t)).

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
    end
  with Binding_rect' (b : Binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (Term_rect' t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.
End Term_rect.


Section term_rect.
  Variable (v : Set).
  Variable (P : term v -> Type).
  Variable (Q : binding v -> Type).
  Variable (R : list (binding v) -> Type).

  Context
    (* (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_Let      : forall rec bs t, R bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : v, P (Var s))
    (H_TyAbs    : forall (s : tyname) (k : Kind) (t : term v), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : v) (t : Ty) (t0 : term v), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : term v, P t -> forall t0 : term v, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some, P (Constant s))
    (H_Builtin  : forall d : func, P (Builtin d))
    (H_TyInst   : forall t : term v, P t -> forall t0 : Ty, P (TyInst t t0))
    (H_Error    : forall t : Ty, P (Error t))
    (H_IWrap    : forall (t t0 : Ty) (t1 : term v), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : term v, P t -> P (Unwrap t)).

  Context
    (H_TermBind     : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind     : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons         : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil          : R nil).

  (*
  Definition bindings_rect' (Binding_rect' : forall (b : binding v), Q b) :=
    fix Bindings_rect' bs :=
    match bs as p return ForallT Q p with
      | nil       => ForallT_nil
      | cons b bs => ForallT_cons (Binding_rect' b) (Bindings_rect' bs)
    end.
    *)

  Definition bindings_rect' (binding_rect' : forall (b : binding v), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Fixpoint term_rect' (t : term v) : P t :=
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
    end
  with binding_rect' (b : binding v) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

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
*)
Definition Mu (f : Type -> Type) (g : Type -> Type) := forall a, (f a -> a) -> (g a -> a) -> a.

Definition unitVal : Term := Constant (Some (ValueOf DefaultUniUnit tt)).


Inductive ZipWith {a} (P : a -> a -> Type) : list a -> list a -> Type :=
  | ZipWithCons : forall x y xs ys, P x y -> ZipWith P xs ys -> ZipWith P (x :: xs) (y :: ys)
  | ZipWithNil  : ZipWith P nil nil.

(* Helper for optionally relating term-bindings, by relating the bound terms *)
Inductive BindingBy (R : Term -> Term -> Type) : Binding -> Binding -> Type :=
  | BB_TermBind: forall t t' s v,
      R t t' ->
      BindingBy R
        (TermBind s v t )
        (TermBind s v t')

  | BB_OtherBind: forall b, BindingBy R b b. (* Todo, enforce no overlap with other constructor? *)


