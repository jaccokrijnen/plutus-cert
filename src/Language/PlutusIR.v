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
Arguments some _ : clear implicits.
(*Inductive some := Some : forall a, valueOf a -> some.*)

(** ** Builtin types *)
Inductive typeIn (u : DefaultUni) :=
  TypeIn : typeIn u.
Arguments TypeIn _ : clear implicits.


Section AST_term.
Context (name tyname : Set).
Context (binderName binderTyname : Set).

(** * Kinds and types *)

(** ** Kinds *)
Inductive kind :=
  | Kind_Base : kind
  | Kind_Arrow : kind -> kind -> kind.

(** ** Types *)
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

Inductive vdecl := VarDecl : binderName -> ty -> vdecl.
Inductive tvdecl := TyVarDecl : binderTyname -> kind -> tvdecl.

(* Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list VDecl -> DTDecl.*)

(* This is a bit in-between hack of having types in the AST and completely ignoring them*)
(* Constructor name and arity, needed for Scott encoding *)
Inductive constr :=
  | Constructor : vdecl -> nat -> constr.

Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> binderName -> list constr -> dtdecl.

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

with binding :=
  | TermBind : Strictness -> vdecl -> term -> binding
  | TypeBind : tvdecl -> ty -> binding
  | DatatypeBind : dtdecl -> binding
.

End AST_term.

(** * Named terms (all variables and binders are strings) *)
Module NamedTerm.

(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)

(* TODO: Coq prints wrong notation for LamAbs type, perhaps just use string
    everywhere? *)
Notation name := string.
Notation tyname := string.
Notation binderName := string.
Notation binderTyname := string.

(* These constructors should treat the type parameter
   as implicit too (this is already correctly generated for the recursive
   constructors. *)

Arguments Ty_Var [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Fun [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Forall [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Builtin [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Lam [tyname]%type_scope [binderTyname]%type_scope.
Arguments Var [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Constant [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Builtin [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TyInst [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Error [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TypeBind [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments DatatypeBind [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.

Arguments VarDecl [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TyVarDecl [binderTyname]%type_scope.
Arguments Datatype [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.

Notation Kind := (kind).
Notation Ty := (ty tyname binderTyname).
Notation VDecl := (vdecl name tyname binderName).
Notation TVDecl := (tvdecl binderTyname).
Notation DTDecl := (dtdecl name tyname binderTyname).
Notation constructor := (constr tyname binderName binderTyname).
Notation Term := (term name tyname binderName binderTyname).
Notation Binding := (binding name tyname binderName binderTyname).

Definition constructorName : constructor -> name := 
  fun c => match c with
  | Constructor (VarDecl n _) _ => n
  end
  .

(** ** Trace of compilation *)
Inductive Pass :=
  | PassRename
  | PassTypeCheck
  | PassInline : list name -> Pass
  | PassDeadCode
  | PassThunkRec
  | PassFloatTerm
  | PassLetNonStrict
  | PassLetTypes
  | PassLetRec
  | PassLetNonRec.

Inductive CompTrace :=
  | CompilationTrace : Term -> list (Pass * Term) -> CompTrace.

End NamedTerm.



(** * De Bruijn terms *)
Module DeBruijnTerm.

From Equations Require Import Equations.

Notation name := nat.
Notation tyname := nat.
Notation binderName := unit.
Notation binderTyname := unit.

Arguments Ty_Var [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Fun [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Forall [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Builtin [tyname]%type_scope [binderTyname]%type_scope.
Arguments Ty_Lam [tyname]%type_scope [binderTyname]%type_scope.
Arguments Var [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Constant [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Builtin [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TyInst [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments Error [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TypeBind [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments DatatypeBind [name]%type_scope [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.

Arguments VarDecl [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.
Arguments TyVarDecl [binderTyname]%type_scope.
Arguments Datatype [tyname]%type_scope [binderName]%type_scope [binderTyname]%type_scope.


Notation Kind := (kind).
Notation Ty := (ty tyname binderTyname).
Notation VDecl := (vdecl tyname binderName binderTyname).
Notation TVDecl := (tvdecl binderTyname).
Notation DTDecl := (dtdecl tyname binderName binderTyname).
Notation constructor := (constr tyname binderName binderTyname).
Notation Term := (term name tyname binderName binderTyname).
Notation Binding := (binding name tyname binderName binderTyname).


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

End DeBruijnTerm.



Section Term_rect.
  Import NamedTerm.

  Unset Implicit Arguments.

  Variable (P : Term -> Type).
  Variable (Q : Binding -> Type).

  Context
    (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : tyname, P (Var s))
    (H_TyAbs    : forall (s : tyname) (k : Kind) (t : Term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : tyname) (t : Ty) (t0 : Term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : Term, P t -> forall t0 : Term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
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
 
Section Term__ind.
  Import NamedTerm.

  Unset Implicit Arguments.

  Variable (P : Term -> Prop).
  Variable (Q : Binding -> Prop).

  Context
    (H_Let      : forall rec bs t, ForallP Q bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s : tyname, P (Var s))
    (H_TyAbs    : forall (s : tyname) (k : Kind) (t : Term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall (s : tyname) (t : Ty) (t0 : Term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : Term, P t -> forall t0 : Term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : Term, P t -> forall t0 : Ty, P (TyInst t t0))
    (H_Error    : forall t : Ty, P (Error t))
    (H_IWrap    : forall (t t0 : Ty) (t1 : Term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : Term, P t -> P (Unwrap t)).

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
    (H_Unwrap   : forall t : term v v' b b', P t -> P (Unwrap t)).

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

  Definition bindings_rect' (binding_rect' : forall (b : binding v v' b b'), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
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
    end
  with binding_rect' (b : binding v v' b b') : Q b :=
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

Definition unitVal : NamedTerm.Term := Constant (Some (ValueOf DefaultUniUnit tt)).


Inductive ZipWith {a} (P : a -> a -> Type) : list a -> list a -> Type :=
  | ZipWithCons : forall x y xs ys, P x y -> ZipWith P xs ys -> ZipWith P (x :: xs) (y :: ys)
  | ZipWithNil  : ZipWith P nil nil.

(* Helper for optionally relating term-bindings, by relating the bound terms *)
Inductive BindingBy (R : NamedTerm.Term -> NamedTerm.Term -> Type) : NamedTerm.Binding -> NamedTerm.Binding -> Type :=
  | BB_TermBind: forall t t' s v,
      R t t' ->
      BindingBy R
        (TermBind s v t )
        (TermBind s v t')

  | BB_OtherBind: forall b, BindingBy R b b. (* Todo, enforce no overlap with other constructor? *)





Declare Custom Entry plutus_term.
Declare Custom Entry plutus_ty.
Declare Custom Entry plutus_kind.

Notation "<{ e }>" := e (e custom plutus_term at level 99).
Notation "<{{ e }}>" := e (e custom plutus_ty at level 99).
Notation "<{{{ e }}}>" := e (e custom plutus_kind at level 99).
Notation "( x )" := x (in custom plutus_term, x at level 99).
Notation "( x )" := x (in custom plutus_ty, x at level 99).
Notation "( x )" := x (in custom plutus_kind, x at level 99).
Notation "x" := x (in custom plutus_term at level 0, x constr at level 0).
Notation "x" := x (in custom plutus_ty at level 0, x constr at level 0).
Notation "x" := x (in custom plutus_kind at level 0, x constr at level 0).
Notation "{ x }" := x (in custom plutus_term at level 1, x constr).
Notation "{ x }" := x (in custom plutus_ty at level 1, x constr).
Notation "{ x }" := x (in custom plutus_kind at level 1, x constr).