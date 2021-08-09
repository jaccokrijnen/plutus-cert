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

Inductive some {f : uni -> Type} :=
  Some : forall {u : uni}, f u -> some.
(*Inductive some := Some : forall a, valueOf a -> some.*)



(** * Kinds and types *)
Local Open Scope string_scope.

(** ** Kinds *)
Inductive Kind :=
  | Kind_Base : Kind
  | Kind_Arrow : Kind -> Kind -> Kind.

(** ** Builtin types *)
Inductive typeIn (u : uni) :=
  TypeIn : typeIn u.
Arguments TypeIn _ : clear implicits.

(** ** Types *)
Inductive Ty :=
  | Ty_Var : name -> Ty
  | Ty_Fun : Ty -> Ty -> Ty
  | Ty_IFix : Ty -> Ty -> Ty
  | Ty_Forall : tyname -> Kind -> Ty -> Ty
  | Ty_Builtin : @some typeIn -> Ty
  | Ty_Lam : tyname -> Kind -> Ty -> Ty
  | Ty_App : Ty -> Ty -> Ty.

(** ** Contexts and lookups *)
Inductive Context :=
  | Nil : Context
  | ConsType : (name * Ty) -> Context -> Context
  | ConsKind : (tyname * Kind) -> Context -> Context.

Delimit Scope context_scope with Context.
Infix ":T:" := ConsType (at level 60, right associativity) : context_scope.
Infix ":K:" := ConsKind (at level 60, right associativity) : context_scope.

Fixpoint appendContexts (ctx1 ctx2 : Context) :=
  match ctx1 with
  | Nil => ctx2
  | ConsType x ctx1' => ConsType x (appendContexts ctx1' ctx2)
  | ConsKind x ctx1' => ConsKind x (appendContexts ctx1' ctx2)
  end.

Fixpoint lookupK (ctx : Context) (X : name) : option Kind := 
  match ctx with
  | ConsKind (Y, K) ctx' => 
    if X =? Y then Coq.Init.Datatypes.Some K else lookupK ctx' X
  | ConsType _ ctx' => lookupK ctx' X
  | Nil => None
  end.

Fixpoint lookupT (ctx : Context) (x : tyname) : option Ty :=
  match ctx with
  | ConsKind _ ctx' => lookupT ctx' x
  | ConsType (y, T) ctx' =>
    if x =? y then Coq.Init.Datatypes.Some T else lookupT ctx' x
  | _ => None
  end.
  
(** ** Kinding of types *)
Reserved Notation "ctx '|-*' ty ':' K" (at level 40, ty at level 0, K at level 0).
Inductive has_kind : Context -> Ty -> Kind -> Prop :=
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
Fixpoint substituteT (X : tyname) (S T : Ty) : Ty :=
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
Inductive EqT : Ty -> Ty -> Prop :=
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
  
(*
  Simplification of attached values in the AST

  In the Haskell AST, Term is a functor and each constructor may have a field of the type parameter
  `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
  (this works because the dumping code is ignoring it)

  TODO: perhaps use a similar approach to the simplification of names, by ignoring the argument
  in each constructor (have to add types for the possible values that can occur when dumping)
*)
Section AST_term.
Context (name : Set).

Inductive vdecl := VarDecl : name -> Ty -> vdecl.
Inductive tvdecl := TyVarDecl : tyname -> Kind -> tvdecl.

(* Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list VDecl -> DTDecl.*)

(* This is a bit in-between hack of having types in the AST and completely ignoring them*)
(* Constructor name and arity, needed for Scott encoding *)
Inductive _constructor :=
  | Constructor : vdecl -> nat -> _constructor.

Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> name -> list _constructor -> dtdecl.

Inductive term :=
  | Let      : Recursivity -> list binding -> term -> term
  | Var      : name -> term
  | TyAbs    : tyname -> Kind -> term -> term
  | LamAbs   : name -> Ty -> term -> term
  | Apply    : term -> term -> term
  | Constant : @some valueOf -> term
  | Builtin  : func -> term
  | TyInst   : term -> Ty -> term
  | Error    : Ty -> term
  | IWrap    : Ty -> Ty -> term -> term
  | Unwrap   : term -> term

with binding :=
  | TermBind : Strictness -> vdecl -> term -> binding
  | TypeBind : tvdecl -> Ty -> binding
  | DatatypeBind : dtdecl -> binding
.


End AST_term.

(* These constructors should treat the type parameter
   as implicit too (this is already correctly generated for the recursive
   constructors. *)

Arguments VarDecl [name]%type_scope.
Arguments Datatype [name]%type_scope.
Arguments Constant [name]%type_scope.
Arguments Builtin [name]%type_scope.
Arguments Error [name]%type_scope.
Arguments TypeBind [name]%type_scope.
Arguments DatatypeBind [name]%type_scope.

Notation VDecl := (vdecl string).
Notation TVDecl := (tvdecl).
Notation DTDecl := (dtdecl string).
Notation constructor := (_constructor string).
Notation Term := (term string).
Notation Binding := (binding string).

Definition constructorName : constructor -> name := 
  fun c => match c with
  | Constructor (VarDecl n _) _ => n
  end
  .

Definition constructorDecl : constructor -> VDecl :=
  fun c => match c with
  | Constructor vd _ => vd
  end.

(** *** Auxiliary functions *)
Definition getName (vd : VDecl) :=
  match vd with
  | VarDecl x _ => x
  end.

Definition getTy (vd : VDecl) :=
  match vd with
  | VarDecl _ T => T
  end.

Definition getTyname (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl X _ => X
  end.

Definition getKind (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl _ K => K
  end.

Definition getMatchFunc (d : DTDecl) :=
  match d with
  | Datatype _ _ matchFunc _ => matchFunc
  end.

Definition branchTy (c : constructor) (R : Ty) : Ty :=
  match c with
  | Constructor (VarDecl x T) _ => 
    match T with
    | Ty_Fun T1 T2 => Ty_Fun T1 R
    | _ => R
    end
  end.

Require Import Coq.Program.Basics.
Open Scope string_scope.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let branchTypes := map (fun c => branchTy c (Ty_Var "R")) cs in
    let branchTypesFolded := fold_right Ty_Fun (Ty_Var "R") branchTypes in
    let indexKinds := map (fun YK => Ty_Lam (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Forall "R" Kind_Base branchTypesFolded) indexKinds
  end.

Definition dataKind (d : DTDecl) : Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    fold_right Kind_Arrow Kind_Base (map getKind YKs)
  end.

Definition constrTy (d : DTDecl) (c : constructor) : Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    let indexTyVars := map (compose Ty_Var getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left Ty_App indexTyVars (Ty_Var (getTyname X)) in
    let branchType := branchTy c indexTyVarsAppliedToX in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply branchType indexForalls
  end.

Definition matchTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let indexTyVars := map (compose Ty_Var getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left Ty_App indexTyVars (Ty_Var (getTyname X)) in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Fun indexTyVarsAppliedToX (fold_left Ty_App indexTyVars (dataTy d))) indexForalls 
  end.

(** *** Binder functions *)
Definition dataBind (d : DTDecl) : tyname * Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (getTyname X, dataKind d)
  end.

Definition constrBind (d : DTDecl) (c : constructor) : name * Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (name * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
    map (constrBind d) cs
  end.

Definition matchBind (d : DTDecl) : name * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (matchFunc, matchTy d)
  end.

Definition binds (b : Binding) : Context :=
  match b with
  | TermBind _ vd _ => ConsType (getName vd, getTy vd) Nil
  | TypeBind tvd ty => ConsKind (getTyname tvd, getKind tvd) Nil
  | DatatypeBind d =>
    let dataB := dataBind d in 
    let constrBs := constrBinds d in
    let constrBs_ctx := fold_right ConsType Nil constrBs in
    let matchB := matchBind d in
    ConsType matchB (appendContexts constrBs_ctx (ConsKind dataB Nil))
  end.

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

(** Types of builtin-functions *)
Definition lookupBuiltinTy (f : DefaultFun) : Ty :=
  let Ty_Int := Ty_Builtin (Some (TypeIn DefaultUniInteger)) in
  let Ty_Bool := Ty_Builtin (Some (TypeIn DefaultUniBool)) in
  let Ty_BS := Ty_Builtin (Some (TypeIn DefaultUniByteString)) in
  let T_Int_Bin := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Int) in
  let T_Int_BinPredicate := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Bool) in
  let T_BS_Bin := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_BS) in
  let T_BS_BinPredicate := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool) in
  let Ty_Char := Ty_Builtin (Some (TypeIn DefaultUniChar)) in
  let Ty_String := Ty_Builtin (Some (TypeIn DefaultUniString)) in
  let Ty_Unit := Ty_Builtin (Some (TypeIn DefaultUniUnit)) in
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
  | IfThenElse => Ty_Forall "a" Kind_Base (Ty_Fun Ty_Bool (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "a") (Ty_Var "a"))))
  | CharToString => Ty_Fun Ty_Char Ty_String
  | Append => Ty_Fun Ty_String (Ty_Fun Ty_String Ty_String)
  | Trace => Ty_Fun Ty_String Ty_Unit (* TODO: figure out if it is the correct type*)
  end.

(** Well-formedness of constructors and bindings *)
Fixpoint typeList (T : Ty) : list Ty :=
  match T with
  | Ty_Fun T1 T2 => cons T1 (typeList T2)
  | _ => nil
  end.

(** Typing of terms *)
Reserved Notation "ctx '|-+' tm ':' T" (at level 40, tm at level 0, T at level 0).
Inductive has_type : Context -> Term -> Ty -> Prop :=
  (* Let-bindings *)
  | T_Let : forall ctx bs t T,
      ctx |-* T : Kind_Base ->
      (forall b, In b bs -> binding_well_formed ctx b) ->
      (appendContexts (fold_right appendContexts Nil (map binds bs)) ctx) |-+ t : T ->
      ctx |-+ (Let NonRec bs t) : T
  | T_LetRec : forall ctx bs t T ctx',
      ctx |-* T : Kind_Base ->
      ctx' = appendContexts (fold_right appendContexts Nil (map binds bs)) ctx ->
      (forall b, In b bs -> binding_well_formed ctx' b) ->
      ctx' |-+ t : T ->
      ctx |-+ (Let Rec bs t) : T
  (* Basic constructs *)
  | T_Var : forall ctx x T,
      lookupT ctx x = Coq.Init.Datatypes.Some T ->
      ctx |-+ (Var x) : T
  | T_TyAbs : forall ctx X K t T,
      (ConsKind (X, K) ctx) |-+ t : T ->
      ctx |-+ (TyAbs X K t) : (Ty_Forall X K T)
  | T_LamAbs : forall ctx x T1 t T2,
      (ConsType (x, T1) ctx) |-+ t : T2 -> 
      ctx |-* T1 : Kind_Base ->
      ctx |-+ (LamAbs x T1 t) : (Ty_Fun T1 T2)
  | T_Apply : forall ctx t1 t2 T1 T2,
      ctx |-+ t1 : (Ty_Fun T1 T2) ->
      ctx |-+ t2 : T1 ->
      ctx |-+ (Apply t1 t2) : T2
  | T_Constant : forall ctx u type,
      ctx |-+ (Constant (Some (ValueOf u type))) : (Ty_Builtin (Some (TypeIn u))) (* TODO *)
  | T_Builtin : forall ctx f,
      ctx |-+ (Builtin f) : (lookupBuiltinTy f)
  | T_TyInst : forall ctx t1 T2 T1 X K2,
      ctx |-+ t1 : (Ty_Forall X K2 T1) ->
      ctx |-* T2 : K2 ->
      ctx |-+ (TyInst t1 T2) : (substituteT X T2 T1)
  | T_Error : forall ctx T,
      ctx |-* T : Kind_Base ->
      ctx |-+ (Error T) : T 
  (* Recursive types *)
  | T_IWrap : forall ctx F T M X K,
      ctx |-+ M : (Ty_App (Ty_App F (Ty_Lam X K (Ty_IFix F (Ty_Var X)))) T) ->
      ctx |-* T : K ->
      ctx |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      ctx |-+ (IWrap F T M) : (Ty_IFix F T)
  | T_Unwrap : forall ctx M F X K T,
      ctx |-+ M : (Ty_IFix F T) ->
      ctx |-* T : K ->
      ctx |-+ (Unwrap M) : (Ty_App (Ty_App F (Ty_Lam X K (Ty_IFix F (Ty_Var X)))) T)
  (* Type equality *)
  | T_Eq : forall ctx t T S,
      ctx |-+ t : S ->
      S =b T ->
      ctx |-+ t : T

  with constructor_well_formed : Context -> constructor -> Prop :=
    | W_Con : forall ctx x T ar,
        (forall U, In U (typeList T) -> ctx |-* U : Kind_Base) ->
        constructor_well_formed ctx (Constructor (VarDecl x T) ar)
  
  with binding_well_formed : Context -> Binding -> Prop :=
    | W_Term : forall ctx s x T t,
        ctx |-* T : Kind_Base ->
        ctx |-+ t : T ->
        binding_well_formed ctx (TermBind s (VarDecl x T) t)
    | W_Type : forall ctx X K T,
        ctx |-* T : K ->
        binding_well_formed ctx (TypeBind (TyVarDecl X K) T)
    | W_Data : forall ctx X YKs cs matchFunc ctx',
        ctx' = fold_right apply ctx (map (fun YK => ConsKind (getTyname YK, getKind YK)) YKs) ->
        (forall c, In c cs -> constructor_well_formed ctx' c) ->
        binding_well_formed ctx (DatatypeBind (Datatype X YKs matchFunc cs))

  where "ctx '|-+' tm ':' T" := (has_type ctx tm T).

#[export] Hint Constructors has_kind : core.
#[export] Hint Constructors EqT : core.
#[export] Hint Constructors has_type : core.
#[export] Hint Constructors constructor_well_formed : core.
#[export] Hint Constructors binding_well_formed : core. 

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


