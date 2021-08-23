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

From Equations Require Equations.

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
    | DefaultUniInteger    => Z
    | DefaultUniByteString => string
    | DefaultUniString     => string
    | DefaultUniChar       => ascii
    | DefaultUniUnit       => unit
    | DefaultUniBool       => bool
  end
  .
Transparent uniType.

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




Inductive valueOf (u : DefaultUni) :=
  ValueOf : uniType u -> valueOf u.
Arguments ValueOf _ _ : clear implicits.

(* Inductive valueOf a :=
  ValueOf : uni a -> a -> valueOf a.
Arguments ValueOf {_} {_}.
*)

Inductive some {f : DefaultUni -> Type} :=
  Some : forall {u : DefaultUni}, f u -> some.
(*Inductive some := Some : forall a, valueOf a -> some.*)

(** ** Builtin types *)
Inductive typeIn (u : DefaultUni) :=
  TypeIn : typeIn u.
Arguments TypeIn _ : clear implicits.

Module Type SIG_VarRep.
Parameter (name tyname binderName binderTyname : Set).
Parameter (eq_name : name -> name -> bool).
Parameter (eq_tyname : tyname -> tyname -> bool).
Parameter (eq_binderName : binderName -> binderName -> bool).
Parameter (eq_binderTyname : binderTyname -> binderTyname -> bool).
End SIG_VarRep.

Module StringVarRep : SIG_VarRep.
Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.
Definition eq_name := String.eqb.
Definition eq_tyname := String.eqb.
Definition eq_binderName := String.eqb.
Definition eq_binderTyname := String.eqb.
End StringVarRep.

Module DeBruijnVarRep <: SIG_VarRep.
Definition name := nat.
Definition tyname := nat.
Definition binderName := unit.
Definition binderTyname := unit.
Definition eq_name := Nat.eqb.
Definition eq_tyname := Nat.eqb.
Definition eq_binderName := fun (x y : unit) => true.
Definition eq_binderTyname := fun (x y : unit) => true.
End DeBruijnVarRep.

Module Type SIG_AST (M_VarRep : SIG_VarRep).
  Parameter (Kind Ty Term Binding : Type).
End SIG_AST.

Module AST_Term (M_VarRep : SIG_VarRep) <: SIG_AST M_VarRep.
Export M_VarRep.

(** * Kinds and types *)

(** ** Kinds *)
Inductive _Kind :=
  | Kind_Base : _Kind
  | Kind_Arrow : _Kind -> _Kind -> _Kind.

Definition Kind := _Kind.

(** ** Types *)
Inductive _Ty :=
  | Ty_Var : M_VarRep.tyname -> _Ty
  | Ty_Fun : _Ty -> _Ty -> _Ty
  | Ty_IFix : _Ty -> _Ty -> _Ty
  | Ty_Forall : M_VarRep.binderTyname -> Kind -> _Ty -> _Ty
  | Ty_Builtin : @some typeIn -> _Ty
  | Ty_Lam : M_VarRep.binderTyname -> Kind -> _Ty -> _Ty
  | Ty_App : _Ty -> _Ty -> _Ty.

Definition Ty := _Ty.

(*
  Simplification of attached values in the AST

  In the Haskell AST, Term is a functor and each constructor may have a field of the type parameter
  `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
  (this works because the dumping code is ignoring it)

  TODO: perhaps use a similar approach to the simplification of names, by ignoring the argument
  in each constructor (have to add types for the possible values that can occur when dumping)
*)

Inductive VDecl := VarDecl : M_VarRep.binderName -> Ty -> VDecl.
Inductive TVDecl := TyVarDecl : M_VarRep.binderTyname -> Kind -> TVDecl.

(* Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list VDecl -> DTDecl.*)

(* This is a bit in-between hack of having types in the AST and completely ignoring them*)
(* Constructor name and arity, needed for Scott encoding *)
Inductive Constr :=
  | Constructor : VDecl -> nat -> Constr.

Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> M_VarRep.binderName -> list Constr -> DTDecl.

Inductive _Term :=
  | Let      : Recursivity -> list _Binding -> _Term -> _Term
  | Var      : M_VarRep.name -> _Term
  | TyAbs    : M_VarRep.binderTyname -> Kind -> _Term -> _Term
  | LamAbs   : M_VarRep.binderName -> Ty -> _Term -> _Term
  | Apply    : _Term -> _Term -> _Term
  | Constant : @some valueOf -> _Term
  | Builtin  : DefaultFun -> _Term
  | TyInst   : _Term -> Ty -> _Term
  | Error    : Ty -> _Term
  | IWrap    : Ty -> Ty -> _Term -> _Term
  | Unwrap   : _Term -> _Term

with _Binding :=
  | TermBind : Strictness -> VDecl -> _Term -> _Binding
  | TypeBind : TVDecl -> _Ty -> _Binding
  | DatatypeBind : DTDecl -> _Binding
.

Definition Term := _Term.
Definition Binding := _Binding.

Definition constructorName : Constr -> M_VarRep.binderName := 
  fun c => match c with
  | Constructor (VarDecl n _) _ => n
  end
  .

(** ** Trace of compilation *)
Inductive Pass :=
| PassRename
| PassTypeCheck
| PassInline : list M_VarRep.name -> Pass
| PassDeadCode
| PassThunkRec
| PassFloatTerm
| PassLetNonStrict
| PassLetTypes
| PassLetRec
| PassLetNonRec.

Inductive CompTrace :=
| CompilationTrace : Term -> list (Pass * Term) -> CompTrace.

Section term_rect.
  Variable (P : Term -> Type).
  Variable (Q : Binding -> Type).
  Variable (R : list Binding -> Type).

  Context
    (* (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_Let      : forall rec bs t, R bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s, P (Var s))
    (H_TyAbs    : forall s k t, P t -> P (TyAbs s k t))
    (H_LamAbs   : forall s t t0 , P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t, P t -> forall t0, P t0 -> P (Apply t t0))
    (H_Constant : forall s, P (Constant s))
    (H_Builtin  : forall d, P (Builtin d))
    (H_TyInst   : forall t, P t -> forall t0, P (TyInst t t0))
    (H_Error    : forall t, P (Error t))
    (H_IWrap    : forall t t0 t1, P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t, P t -> P (Unwrap t)).

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

  Definition bindings_rect' (binding_rect' : forall (b : Binding), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Fixpoint term_rect' (t : Term) : P t :=
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
  with binding_rect' (b : Binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

End AST_Term.

(** * Named terms (all variables and binders are strings) *)
Module NamedTerm := AST_Term StringVarRep.

Module DeBruijnTerm.
Import Equations.
Module Export AST := AST_Term DeBruijnVarRep.


Fixpoint shift_Ty' (k c : nat) (T : Ty) : Ty :=
  match T with
  | Ty_Var X => if X <? c then Ty_Var X else Ty_Var (k + X)
  | Ty_Fun T1 T2 => Ty_Fun (shift_Ty' k c T1) (shift_Ty' k c T2)
  | Ty_IFix F T0 => Ty_IFix (shift_Ty' k c F) (shift_Ty' k c T0)
  | Ty_Forall bX K T => Ty_Forall bX K (shift_Ty' k (S c) T)
  | Ty_Builtin u => Ty_Builtin u
  | Ty_Lam bX K1 T => Ty_Lam bX K1 (shift_Ty' k (S c) T)
  | Ty_App T1 T2 => Ty_App (shift_Ty' k c T1) (shift_Ty' k c T2)
  end.

Definition shift_Ty (T : Ty) := shift_Ty' 1 0 T.

Equations shift_Term' : nat -> nat -> Term -> Term := {
  shift_Term' k c (Let NonRec bs t0) => Let NonRec (shift_Bindings' k c bs) (shift_Term' k (length bs + c) t0) ;
  shift_Term' k c (Let Rec bs t0) => Let Rec (shift_Bindings' k (length bs + c) bs (* TODO: shift by c or more? *)) (shift_Term' k (length bs + c) t0) ;
  shift_Term' k c (Var x) => if x <? c then Var x else Var (k + x) ;
  shift_Term' k c (TyAbs bX K t0) => TyAbs bX K (shift_Term' k (S c) t0) ;
  shift_Term' k c (LamAbs bx T t0) => LamAbs bx (shift_Ty' k c T) (shift_Term' k (S c) t0) ;
  shift_Term' k c (Apply t1 t2) => Apply (shift_Term' k c t1) (shift_Term' k c t2) ;
  shift_Term' k c (Constant u) => Constant u ;
  shift_Term' k c (Builtin d) => Builtin d ;
  shift_Term' k c (TyInst t0 T) => TyInst (shift_Term' k c t0) (shift_Ty' k c T) ;
  shift_Term' k c (Error T) => Error (shift_Ty' k c T) ;
  shift_Term' k c (IWrap F T t0) => IWrap (shift_Ty' k c F) (shift_Ty' k c T) (shift_Term' k c t0) ;
  shift_Term' k c (Unwrap t0) => Unwrap (shift_Term' k c t0) }

where shift_Bindings' : nat -> nat -> list Binding -> list Binding := {
  shift_Bindings' k c nil => nil ;
  shift_Bindings' k c (TermBind s (VarDecl bn T) t :: bs) => TermBind s (VarDecl bn (shift_Ty' k c T)) (shift_Term' k c t) :: shift_Bindings' k c bs ;
  shift_Bindings' k c (TypeBind tvd T :: bs) => TypeBind tvd (shift_Ty' k c T) :: shift_Bindings' k c bs ;
  shift_Bindings' k c (DatatypeBind (Datatype X YKs matchFunc cs) :: bs) => DatatypeBind (Datatype X YKs matchFunc (shift_Constructors' k c cs)) :: shift_Bindings' k c bs} 

where shift_Constructors' : nat -> nat -> list Constr -> list Constr := {
  shift_Constructors' k c nil => nil ;
  shift_Constructors' k c (Constructor (VarDecl bn T) ar :: cs) => Constructor (VarDecl bn (shift_Ty' k c T)) ar :: shift_Constructors' k c cs }. 

Definition shift_term (t : Term) := shift_Term' 1 0 t.

End DeBruijnTerm.

Section Term_rect.
  Import NamedTerm.

  Unset Implicit Arguments.

  Variable (P : Term -> Type).
  Variable (Q : Binding -> Type).

  Context
    (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s, P (Var s))
    (H_TyAbs    : forall s k t, P t -> P (TyAbs s k t))
    (H_LamAbs   : forall s t t0, P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t, P t -> forall t0, P t0 -> P (Apply t t0))
    (H_Constant : forall s, P (Constant s))
    (H_Builtin  : forall d, P (Builtin d))
    (H_TyInst   : forall t, P t -> forall t0, P (TyInst t t0))
    (H_Error    : forall t, P (Error t))
    (H_IWrap    : forall t t0 t1, P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t, P t -> P (Unwrap t)).

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

Definition unitVal : NamedTerm.Term := NamedTerm.Constant (Some (ValueOf DefaultUniUnit tt)).


Inductive ZipWith {a} (P : a -> a -> Type) : list a -> list a -> Type :=
  | ZipWithCons : forall x y xs ys, P x y -> ZipWith P xs ys -> ZipWith P (x :: xs) (y :: ys)
  | ZipWithNil  : ZipWith P nil nil.

(* Helper for optionally relating term-bindings, by relating the bound terms *)
Inductive BindingBy (R : NamedTerm.Term -> NamedTerm.Term -> Type) : NamedTerm.Binding -> NamedTerm.Binding -> Type :=
  | BB_TermBind: forall t t' s v,
      R t t' ->
      BindingBy R
        (NamedTerm.TermBind s v t )
        (NamedTerm.TermBind s v t')

  | BB_OtherBind: forall b, BindingBy R b b. (* Todo, enforce no overlap with other constructor? *)


