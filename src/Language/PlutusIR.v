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

(* JORIS: START *)
Section Types.

Open Scope string_scope.

(** ** Kinds *)

Inductive Kind' :=
  | Kind_Base : Kind' 
  | Kind_Arrow : Kind' -> Kind' -> Kind'.

(** ** Types *)
Inductive Ty' :=
  | Ty_Var : string -> Ty'
  | Ty_Fun : Ty' -> Ty' -> Ty'
  | Ty_IFix : Ty' -> Ty' -> Ty'
  | Ty_Forall : tyname -> Kind' -> Ty' -> Ty'
  | Ty_Builtin : uni -> Ty'
  | Ty_Lam : tyname -> Kind' -> Ty' -> Ty'
  | Ty_App : Ty' -> Ty' -> Ty'.

(** ** Contexts and lookups *)
Inductive Context :=
  | Nil : Context
  | ConsType : (string * Ty') -> Context -> Context
  | ConsKind : (string * Kind') -> Context -> Context.

Fixpoint lookupK (ctx : Context) (X : string) : option Kind' := 
  match ctx with
  | ConsKind (Y, K) ctx' => 
    if X =? Y then Coq.Init.Datatypes.Some K else lookupK ctx' X
  | _ => None
  end.

Fixpoint lookupT (ctx : Context) (x : string) : option Ty' :=
  match ctx with
  | ConsType (y, T) ctx' =>
    if x =? y then Coq.Init.Datatypes.Some T else lookupT ctx' x
  | _ => None
  end.

(** ** Kinding of types *)
Reserved Notation "ctx '|-*' ty ':' K" (at level 40, ty at level 0, K at level 0).
Inductive has_kind : Context -> Ty' -> Kind' -> Prop :=
  | K_Var : forall ctx X K,
      lookupK ctx X = Coq.Init.Datatypes.Some K ->
      ctx |-* (Ty_Var X) : K
  | K_Fun : forall ctx T1 T2,
      ctx |-* T1 : Kind_Base ->
      ctx |-* T2 : Kind_Base ->
      ctx |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall ctx F T K,
      ctx |-* T : K ->
      ctx |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      ctx |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall ctx X K T,
      (ConsKind (X, K) ctx) |-* T : Kind_Base ->
      ctx |-* (Ty_Forall X K T) : Kind_Base
  (* Note on builtins: At the moment of writing this, all built-in types are of base kind. *)
  | K_Builtin : forall ctx u,
      ctx |-* (Ty_Builtin u) : Kind_Base 
  | K_Lam : forall ctx X K1 T K2,
      (ConsKind (X, K1) ctx) |-* T : K2 ->
      ctx |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall ctx T1 T2 K1 K2,
      ctx |-* T1 : (Kind_Arrow K1 K2) ->
      ctx |-* T2 : K1 ->
      ctx |-* (Ty_App T1 T2) : K2
where "ctx '|-*' ty ':' K" := (has_kind ctx ty K).

(** ** Substitution in types *)
Fixpoint substituteT (X : string) (S T : Ty') : Ty' :=
  match T with
  | Ty_Var Y => 
    if X =? Y then S else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X S T1) (substituteT X S T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X S F) (substituteT X S T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X S T')
  | Ty_Builtin u => 
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X S T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X S T1) (substituteT X S T2)
  end.

(** ** Type equality *)
Reserved Notation "T1 '=b' T2" (at level 40).
Inductive EqT : Ty' -> Ty' -> Prop :=
  (* Beta-reduction *)
  | EqT_Beta : forall X K T1 T2,
      Ty_App (Ty_Lam X K T1) T2 =b substituteT X T2 T1
  (* Reflexivity, Symmetry and Transitivity*)
  | EqT_Refl : forall T,
      T =b T
  | EqT_Symm : forall T S,
      T =b S ->
      S =b T
  | EqT_Trans : forall S U T,
      S =b U ->
      U =b T ->
      S =b T
  (* Congruence *)
  | EqT_Fun : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_Fun S1 T1 =b Ty_Fun S2 T2
  | EqT_Forall : forall X K S T,
      S =b T ->
      Ty_Forall X K S =b Ty_Forall X K T
  | EqT_Lam : forall X K S T,
      S =b T ->
      Ty_Lam X K S =b Ty_Lam X K T
  | EqT_App : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_App S1 T1 =b Ty_App S2 T2
where "T1 '=b' T2" := (EqT T1 T2).

(** ** Terms *)
Section Terms.
Context (name : Set).

Inductive term :=
  | Let      : Recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : tyname -> Kind' -> term -> term
  | LamAbs   : name -> Ty' -> term -> term
  | Apply    : term -> term -> term
  | Constant : some -> term
  | Builtin  : func -> term
  | TyInst   : term -> Ty' -> term
  | Error    : Ty' -> term
  | IWrap    : Ty' -> Ty' -> term -> term
  | Unwrap   : term -> term

with binding :=
  | TermBind : Strictness -> VDecl -> term -> binding
  | TypeBind : TVDecl -> Ty -> binding
  | DatatypeBind : DTDecl -> binding
.

End Terms.

(** Types of builtin-functions *)
Definition lookupBuiltinTy (f : DefaultFun) : Ty' :=
  let Ty_Int := Ty_Builtin DefaultUniInteger in
  let Ty_Bool := Ty_Builtin DefaultUniBool in
  let Ty_BS := Ty_Builtin DefaultUniByteString in
  let T_Int_Bin := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Int) in
  let T_Int_BinPredicate := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Bool) in
  let T_BS_Bin := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_BS) in
  let T_BS_BinPredicate := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool) in
  let Ty_Char := Ty_Builtin DefaultUniChar in
  let Ty_String := Ty_Builtin DefaultUniString in
  let Ty_Unit := Ty_Builtin DefaultUniUnit in
  match f with
  | AddInteger => T_Int_Bin
  | SubtractInteger => T_Int_Bin
  | MultiplyInteger => T_Int_Bin
  | DivideInteger => T_Int_Bin
  | QuotientInteger => T_Int_Bin
  | RemainderInteger => T_Int_Bin
  | ModInteger => T_Int_Bin
  | LessThanInteger => T_Int_BinPredicate
  | LessThanEqInteger => T_Int_BinPredicate
  | GreaterThanInteger => T_Int_BinPredicate
  | GreaterThanEqInteger => T_Int_BinPredicate
  | EqInteger => T_Int_BinPredicate
  | Concatenate => T_BS_Bin
  | TakeByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | DropByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | SHA2 => Ty_Fun Ty_BS Ty_BS
  | SHA3 => Ty_Fun Ty_BS Ty_BS
  | VerifySignature => Ty_Fun Ty_BS (Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool))
  | EqByteString => T_BS_BinPredicate
  | LtByteString => T_BS_BinPredicate
  | GtByteString => T_BS_BinPredicate
  | IfThenElse => Ty_Forall "a" Kind_Base (Ty_Fun Ty_Bool (Ty_Fun (Ty_Var "a") (Ty_Var "a")))
  | CharToString => Ty_Fun Ty_Char Ty_String
  | Append => Ty_Fun Ty_String (Ty_Fun Ty_String Ty_String)
  | Trace => Ty_Fun Ty_String Ty_Unit (* TODO: figure out if it is the correct type*)
  end.

(** Typing of terms *)
Reserved Notation "ctx '|-' tm ':' T" (at level 40, tm at level 0, T at level 0).
Inductive has_type : Context -> term string -> Ty' -> Prop :=
  (* TODO : Let-bindings *)
  (* 
  | T_Let 
  *)
  | T_Var : forall ctx x T,
      lookupT ctx x = Coq.Init.Datatypes.Some T ->
      ctx |- (Var x) : T
  | T_TyAbs : forall ctx X K t T,
      (ConsKind (X, K) ctx) |- t : T ->
      ctx |- (TyAbs X K t) : (Ty_Forall X K T)
  | T_LamAbs : forall ctx x T1 t T2,
      (ConsType (x, T1) ctx) |- t : T2 -> 
      ctx |-* T1 : Kind_Base ->
      ctx |- (LamAbs x T1 t) : (Ty_Fun T1 T2)
  | T_Apply : forall ctx t1 t2 T1 T2,
      ctx |- t1 : (Ty_Fun T1 T2) ->
      ctx |- t2 : T1 ->
      ctx |- (Apply t1 t2) : T2
  | T_Constant : forall ctx u type,
      ctx |- (Constant _ (Some (ValueOf u type))) : (Ty_Builtin u) (* TODO *)
  | T_Builtin : forall ctx f,
      ctx |- (Builtin _ f) : (lookupBuiltinTy f)
  | T_TyInst : forall ctx t1 T2 T1 X K2,
      ctx |- t1 : (Ty_Forall X K2 T1) ->
      ctx |-* T2 : K2 ->
      ctx |- (TyInst t1 T2) : (substituteT X T2 T1)
  | T_Error : forall ctx T,
      ctx |-* T : Kind_Base ->
      ctx |- (Error _ T) : T 
  (* TODO : Recursive types *)
  (*
  | T_IWrap
  | T_Unwrap 
  *)
where "ctx '|-' tm ':' T" := (has_type ctx tm T).

End Types.
(* JORIS: END *)


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


