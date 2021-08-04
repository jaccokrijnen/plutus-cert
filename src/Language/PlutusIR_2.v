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

(* Inductive valueOf a :=
  ValueOf : uni a -> a -> valueOf a.
Arguments ValueOf {_} {_}.
*)

Inductive some {f : uni -> Type} :=
  Some : forall {u : uni}, f u -> some.
(*Inductive some := Some : forall a, valueOf a -> some.*)

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
  | Ty_Var : string -> Ty
  | Ty_Fun : Ty -> Ty -> Ty
  | Ty_IFix : Ty -> Ty -> Ty
  | Ty_Forall : tyname -> Kind -> Ty -> Ty
  | Ty_Builtin : @some typeIn -> Ty
  | Ty_Lam : tyname -> Kind -> Ty -> Ty
  | Ty_App : Ty -> Ty -> Ty.

(** ** Contexts and lookups *)
Inductive Context :=
  | Nil : Context
  | ConsType : (string * Ty) -> Context -> Context
  | ConsKind : (string * Kind) -> Context -> Context.

Fixpoint appendContexts (ctx1 ctx2 : Context) :=
  match ctx1 with
  | Nil => ctx2
  | ConsType x ctx1' => ConsType x (appendContexts ctx1' ctx2)
  | ConsKind x ctx1' => ConsKind x (appendContexts ctx1' ctx2)
  end.

Open Scope string_scope.

Fixpoint lookupK (ctx : Context) (X : string) : option Kind := 
  match ctx with
  | ConsKind (Y, K) ctx' => 
    if X =? Y then Coq.Init.Datatypes.Some K else lookupK ctx' X
  | _ => None
  end.

Fixpoint lookupT (ctx : Context) (x : string) : option Ty :=
  match ctx with
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
Fixpoint substituteT (X : string) (S T : Ty) : Ty :=
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

(** ** Declarations *)
(*
  Simplification of attached values in the AST

  In the Haskell AST, Term is a functor and each constructor may have a field of the type parameter
  `a`. Since this seems to be used only for storing intermediate compiler data, it is ignored here.
  (this works because the dumping code is ignoring it)

  TODO: perhaps use a similar approach to the simplification of names, by ignoring the argument
  in each constructor (have to add types for the possible values that can occur when dumping)
*)

(* Grammar from Kereev et al. included below. *)
(* bindings b     ::= x : T = t     *)
Inductive VDecl := VarDecl : name -> Ty -> VDecl.
(*                    X :: K = T    *)
Inductive TVDecl := TyVarDecl : tyname -> Kind -> TVDecl.
(*                    data X = (<ol> Y :: K <\ol>) = <ol> c <\ol> with x          *)
Inductive DTDecl := Datatype : TVDecl -> list TVDecl -> name -> list VDecl -> DTDecl.

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

Definition branchTy (c : VDecl) (R : Ty) : Ty :=
  match c with
  | VarDecl x T => Ty_Fun T R
  end.

Require Import Coq.Program.Basics.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let branchTypes := map (fun c => branchTy c (Ty_Var "R")) cs in
    let branchTypesFolded := fold_right Ty_Fun (Ty_Var "R") branchTypes in
    let indexKinds := map (fun YK => Ty_Lam (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Forall "R" Kind_Base branchTypesFolded) indexKinds
  end.

Definition YK1 := TyVarDecl "X" (Kind_Arrow Kind_Base Kind_Base).
Definition YK2 := TyVarDecl "Y" (Kind_Base). 
Definition c1 := VarDecl "c1" (Ty_Fun (Ty_Var "b") (Ty_Var "b")).
Definition c2 := VarDecl "c2" (Ty_Fun (Ty_Fun (Ty_Var "b") (Ty_Var "b")) (Ty_Fun (Ty_Var "b") (Ty_Var "b"))).
Definition d1 := Datatype (TyVarDecl "d1" Kind_Base) (cons YK1 (cons YK2 nil)) "match_d1" (cons c1 (cons c2 nil)).
Definition d2 := Datatype (TyVarDecl "d2" Kind_Base) (cons YK2 nil) "match_d2" (cons c1 nil).

Example test_dataTy : 
  dataTy d1 =
    Ty_Lam "X" (Kind_Arrow Kind_Base Kind_Base) (
      Ty_Lam "Y" Kind_Base (
        Ty_Forall "R" Kind_Base (Ty_Fun (branchTy c1 (Ty_Var "R")) (Ty_Fun (branchTy c2 (Ty_Var "R")) (Ty_Var "R")))
      )
    ).
Proof. auto. Qed.

Definition dataKind (d : DTDecl) : Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    fold_right Kind_Arrow Kind_Base (map getKind YKs)
  end.

Compute (dataKind d1).

Definition constrTy (d : DTDecl) (c : VDecl) : Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, VarDecl x T =>
    let indexTyVars := map (compose Ty_Var getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left Ty_App indexTyVars (Ty_Var (getTyname X)) in
    let branchType := branchTy c indexTyVarsAppliedToX in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply branchType indexForalls
  end.

Compute (constrTy d1 c1).
Compute (constrTy d1 c2).

Definition matchTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let indexTyVars := map (compose Ty_Var getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left Ty_App indexTyVars (Ty_Var (getTyname X)) in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Fun indexTyVarsAppliedToX (fold_left Ty_App indexTyVars (dataTy d))) indexForalls 
  end.

Compute (matchTy d1).
Compute (matchTy d2).

(** ** Terms *)
Section AST_term.
Context (name : Set).

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
  | TermBind : Strictness -> VDecl -> term -> binding
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

(** *** Binder functions *)
Definition dataBind (d : DTDecl) : string * Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (getTyname X, dataKind d)
  end.

Definition constrBind (d : DTDecl) (c : VDecl) : string * Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, VarDecl x T =>
    (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (string * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
    map (constrBind d) cs
  end.

Definition matchBind (d : DTDecl) : string * Ty :=
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
    ConsType (getMatchFunc d, matchTy d) (ConsType matchB (appendContexts constrBs_ctx (ConsKind dataB Nil)))
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

Definition test_trace := CompilationTrace 
    (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("ByteString") (Unique (0)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (11)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (12))) (cons (VarDecl (Name ("True") (Unique (13))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (cons (VarDecl (Name ("False") (Unique (14))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (nil))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySignature") (Unique (57))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))))) (LamAbs (Name ("arg") (Unique (53))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (54))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (55))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (56))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (56))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Apply (Builtin (VerifySignature)) (Var (Name ("arg") (Unique (53))))) (Var (Name ("arg") (Unique (54))))) (Var (Name ("arg") (Unique (55)))))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("String") (Unique (2)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (60)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (61))) (cons (VarDecl (Name ("Unit") (Unique (62))) (Ty_Var (TyName (Name ("Unit") (Unique (60)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (70))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))))) (LamAbs (Name ("arg") (Unique (68))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Apply (LamAbs (Name ("b") (Unique (69))) (Ty_Builtin (Some (TypeIn (DefaultUniUnit)))) (Var (Name ("Unit") (Unique (62))))) (Apply (Builtin (Trace)) (Var (Name ("arg") (Unique (68)))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (1)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("takeByteString") (Unique (5))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (TakeByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (27))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (8))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA3))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (7))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA2))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (32))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (31))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (28))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (44))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (41))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (42))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (43))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (43))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanInteger)) (Var (Name ("arg") (Unique (41))))) (Var (Name ("arg") (Unique (42))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (48))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (45))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (46))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (47))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (47))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (45))))) (Var (Name ("arg") (Unique (46))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (20))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (17))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (18))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (19))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (LtByteString)) (Var (Name ("arg") (Unique (17))))) (Var (Name ("arg") (Unique (18))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanInteger") (Unique (36))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (34))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (35))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (35))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanInteger)) (Var (Name ("arg") (Unique (33))))) (Var (Name ("arg") (Unique (34))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanEqInteger") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (37))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (39))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (39))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GreaterThanEqInteger)) (Var (Name ("arg") (Unique (37))))) (Var (Name ("arg") (Unique (38))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanByteString") (Unique (24))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (21))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (22))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (23))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (23))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (GtByteString)) (Var (Name ("arg") (Unique (21))))) (Var (Name ("arg") (Unique (22))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (64))) (Ty_Forall (TyName (Name ("a") (Unique (63)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("a") (Unique (63)))))))) (TyAbs (TyName (Name ("e") (Unique (58)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (59))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Error (Ty_Var (TyName (Name ("e") (Unique (58))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (52))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (49))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (50))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (51))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (51))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqInteger)) (Var (Name ("arg") (Unique (49))))) (Var (Name ("arg") (Unique (50))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (16))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))))) (LamAbs (Name ("arg") (Unique (9))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (10))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (15))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("b") (Unique (15))))) (Var (Name ("True") (Unique (13))))) (Var (Name ("False") (Unique (14)))))) (Apply (Apply (Builtin (EqByteString)) (Var (Name ("arg") (Unique (9))))) (Var (Name ("arg") (Unique (10))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (66))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (25))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("dropByteString") (Unique (6))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (DropByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (29))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("concatenate") (Unique (4))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (Concatenate))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Char") (Unique (3)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniChar))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("charToString") (Unique (67))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniChar)))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))))) (Builtin (CharToString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (65))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))))) (Builtin (Append))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (26))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (72))) (cons (VarDecl (Name ("Fixed") (Unique (73))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (74))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (11)))))) (Var (Name ("False") (Unique (14))))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("wild") (Unique (78))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (Var (Name ("ds") (Unique (75))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (72)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Ty_Var (TyName (Name ("Bool") (Unique (11))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (48)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (60))))) (Var (Name ("keep") (Unique (77)))))) (Var (Name ("Unit") (Unique (62))))))))))))))))))))))))))))))))))))))))))) (cons ((PassRename,Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("ByteString") (Unique (82)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (83)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (86))) (cons (VarDecl (Name ("True") (Unique (84))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (cons (VarDecl (Name ("False") (Unique (85))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (nil))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySignature") (Unique (87))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83))))))))) (LamAbs (Name ("arg") (Unique (88))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (89))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (90))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (91))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (91))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Apply (Builtin (VerifySignature)) (Var (Name ("arg") (Unique (88))))) (Var (Name ("arg") (Unique (89))))) (Var (Name ("arg") (Unique (90)))))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("String") (Unique (92)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (93)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (95))) (cons (VarDecl (Name ("Unit") (Unique (94))) (Ty_Var (TyName (Name ("Unit") (Unique (93)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (96))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))))) (LamAbs (Name ("arg") (Unique (97))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Apply (LamAbs (Name ("b") (Unique (98))) (Ty_Builtin (Some (TypeIn (DefaultUniUnit)))) (Var (Name ("Unit") (Unique (94))))) (Apply (Builtin (Trace)) (Var (Name ("arg") (Unique (97)))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (99)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("takeByteString") (Unique (100))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (TakeByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (101))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (102))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA3))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (103))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA2))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (104))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (105))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (106))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (107))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (108))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (109))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (110))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (111))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (111))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LessThanInteger)) (Var (Name ("arg") (Unique (109))))) (Var (Name ("arg") (Unique (110))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (112))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (113))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (114))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (115))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (115))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (113))))) (Var (Name ("arg") (Unique (114))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (116))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (117))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (118))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (119))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (119))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LtByteString)) (Var (Name ("arg") (Unique (117))))) (Var (Name ("arg") (Unique (118))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanInteger") (Unique (120))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (121))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (122))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (123))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (123))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GreaterThanInteger)) (Var (Name ("arg") (Unique (121))))) (Var (Name ("arg") (Unique (122))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanEqInteger") (Unique (124))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (125))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (126))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (127))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (127))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GreaterThanEqInteger)) (Var (Name ("arg") (Unique (125))))) (Var (Name ("arg") (Unique (126))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanByteString") (Unique (128))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (129))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (130))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (131))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (131))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GtByteString)) (Var (Name ("arg") (Unique (129))))) (Var (Name ("arg") (Unique (130))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (132))) (Ty_Forall (TyName (Name ("a") (Unique (133)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Ty_Var (TyName (Name ("a") (Unique (133)))))))) (TyAbs (TyName (Name ("e") (Unique (134)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (135))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Error (Ty_Var (TyName (Name ("e") (Unique (134))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (136))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (137))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (138))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (139))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (139))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (EqInteger)) (Var (Name ("arg") (Unique (137))))) (Var (Name ("arg") (Unique (138))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (140))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (141))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (142))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (143))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (143))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (EqByteString)) (Var (Name ("arg") (Unique (141))))) (Var (Name ("arg") (Unique (142))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (144))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (145))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("dropByteString") (Unique (146))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (DropByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (147))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("concatenate") (Unique (148))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (Concatenate))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Char") (Unique (149)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniChar))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("charToString") (Unique (150))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniChar)))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))))) (Builtin (CharToString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (151))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))))) (Builtin (Append))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (152))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (153)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (156))) (cons (VarDecl (Name ("Fixed") (Unique (154))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (153))))))) (cons (VarDecl (Name ("Never") (Unique (155))) (Ty_Var (TyName (Name ("EndDate") (Unique (153)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (157))) (Ty_Var (TyName (Name ("EndDate") (Unique (153))))) (LamAbs (Name ("ds") (Unique (158))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (159))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("False") (Unique (85))))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("wild") (Unique (160))) (Ty_Var (TyName (Name ("EndDate") (Unique (153)))))) (Var (Name ("ds") (Unique (157))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (156)))) (Var (Name ("ds") (Unique (157))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Ty_Var (TyName (Name ("Bool") (Unique (83))))))) (LamAbs (Name ("n") (Unique (161))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (162))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (112)))) (Var (Name ("n") (Unique (161))))) (Var (Name ("ds") (Unique (158)))))))) (LamAbs (Name ("thunk") (Unique (163))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Var (Name ("keep") (Unique (159)))))) (Var (Name ("Unit") (Unique (94)))))))))))))))))))))))))))))))))))))))))))) (cons ((PassTypeCheck,Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("ByteString") (Unique (82)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (83)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (86))) (cons (VarDecl (Name ("True") (Unique (84))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (cons (VarDecl (Name ("False") (Unique (85))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (nil))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("verifySignature") (Unique (87))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83))))))))) (LamAbs (Name ("arg") (Unique (88))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (89))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (90))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (91))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (91))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Apply (Builtin (VerifySignature)) (Var (Name ("arg") (Unique (88))))) (Var (Name ("arg") (Unique (89))))) (Var (Name ("arg") (Unique (90)))))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("String") (Unique (92)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (93)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (95))) (cons (VarDecl (Name ("Unit") (Unique (94))) (Ty_Var (TyName (Name ("Unit") (Unique (93)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("trace") (Unique (96))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))))) (LamAbs (Name ("arg") (Unique (97))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Apply (LamAbs (Name ("b") (Unique (98))) (Ty_Builtin (Some (TypeIn (DefaultUniUnit)))) (Var (Name ("Unit") (Unique (94))))) (Apply (Builtin (Trace)) (Var (Name ("arg") (Unique (97)))))))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Integer") (Unique (99)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("takeByteString") (Unique (100))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (TakeByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("subtractInteger") (Unique (101))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (SubtractInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha3_") (Unique (102))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA3))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("sha2_") (Unique (103))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))))) (Builtin (SHA2))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("remainderInteger") (Unique (104))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (RemainderInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("quotientInteger") (Unique (105))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (QuotientInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("multiplyInteger") (Unique (106))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (MultiplyInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("modInteger") (Unique (107))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (ModInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanInteger") (Unique (108))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (109))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (110))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (111))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (111))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LessThanInteger)) (Var (Name ("arg") (Unique (109))))) (Var (Name ("arg") (Unique (110))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (112))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (113))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (114))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (115))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (115))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (113))))) (Var (Name ("arg") (Unique (114))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanByteString") (Unique (116))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (117))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (118))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (119))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (119))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (LtByteString)) (Var (Name ("arg") (Unique (117))))) (Var (Name ("arg") (Unique (118))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanInteger") (Unique (120))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (121))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (122))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (123))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (123))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GreaterThanInteger)) (Var (Name ("arg") (Unique (121))))) (Var (Name ("arg") (Unique (122))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanEqInteger") (Unique (124))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (125))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (126))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (127))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (127))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GreaterThanEqInteger)) (Var (Name ("arg") (Unique (125))))) (Var (Name ("arg") (Unique (126))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("greaterThanByteString") (Unique (128))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (129))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (130))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (131))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (131))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (GtByteString)) (Var (Name ("arg") (Unique (129))))) (Var (Name ("arg") (Unique (130))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("error") (Unique (132))) (Ty_Forall (TyName (Name ("a") (Unique (133)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Ty_Var (TyName (Name ("a") (Unique (133)))))))) (TyAbs (TyName (Name ("e") (Unique (134)))) (Kind_Base) (LamAbs (Name ("thunk") (Unique (135))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Error (Ty_Var (TyName (Name ("e") (Unique (134))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsInteger") (Unique (136))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (137))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (138))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (139))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (139))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (EqInteger)) (Var (Name ("arg") (Unique (137))))) (Var (Name ("arg") (Unique (138))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("equalsByteString") (Unique (140))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))))) (LamAbs (Name ("arg") (Unique (141))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (LamAbs (Name ("arg") (Unique (142))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Apply (LamAbs (Name ("b") (Unique (143))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("b") (Unique (143))))) (Var (Name ("True") (Unique (84))))) (Var (Name ("False") (Unique (85)))))) (Apply (Apply (Builtin (EqByteString)) (Var (Name ("arg") (Unique (141))))) (Var (Name ("arg") (Unique (142))))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyString") (Unique (144))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))) (Constant (Some (ValueOf (DefaultUniString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("emptyByteString") (Unique (145))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))) (Constant (Some (ValueOf (DefaultUniByteString) (""))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("dropByteString") (Unique (146))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (DropByteString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("divideInteger") (Unique (147))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (DivideInteger))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("concatenate") (Unique (148))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniByteString)))) (Ty_Builtin (Some (TypeIn (DefaultUniByteString))))))) (Builtin (Concatenate))) (nil)) (Let (NonRec) (cons (TypeBind (TyVarDecl (TyName (Name ("Char") (Unique (149)))) (Kind_Base)) (Ty_Builtin (Some (TypeIn (DefaultUniChar))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("charToString") (Unique (150))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniChar)))) (Ty_Builtin (Some (TypeIn (DefaultUniString)))))) (Builtin (CharToString))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("appendString") (Unique (151))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniString)))) (Ty_Builtin (Some (TypeIn (DefaultUniString))))))) (Builtin (Append))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("addInteger") (Unique (152))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))))) (Builtin (AddInteger))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (153)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (156))) (cons (VarDecl (Name ("Fixed") (Unique (154))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (153))))))) (cons (VarDecl (Name ("Never") (Unique (155))) (Ty_Var (TyName (Name ("EndDate") (Unique (153)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (157))) (Ty_Var (TyName (Name ("EndDate") (Unique (153))))) (LamAbs (Name ("ds") (Unique (158))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (159))) (Ty_Var (TyName (Name ("Bool") (Unique (83)))))) (Var (Name ("False") (Unique (85))))) (nil)) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("wild") (Unique (160))) (Ty_Var (TyName (Name ("EndDate") (Unique (153)))))) (Var (Name ("ds") (Unique (157))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (156)))) (Var (Name ("ds") (Unique (157))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Ty_Var (TyName (Name ("Bool") (Unique (83))))))) (LamAbs (Name ("n") (Unique (161))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (162))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (112)))) (Var (Name ("n") (Unique (161))))) (Var (Name ("ds") (Unique (158)))))))) (LamAbs (Name ("thunk") (Unique (163))) (Ty_Var (TyName (Name ("Unit") (Unique (93))))) (Var (Name ("keep") (Unique (159)))))) (Var (Name ("Unit") (Unique (94)))))))))))))))))))))))))))))))))))))))))))) (cons ((PassDeadCode,Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (1)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (4))) (cons (VarDecl (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (cons (VarDecl (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (nil))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (11)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (13))) (cons (VarDecl (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (74))) (cons (VarDecl (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("False") (Unique (3))))) (nil)) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("keep") (Unique (77)))))) (Var (Name ("Unit") (Unique (12))))))))))))) (cons ((PassInline (cons (Name ("keep") (Unique (77))) (nil)),Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (1)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (4))) (cons (VarDecl (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (cons (VarDecl (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (nil))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (11)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (13))) (cons (VarDecl (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (74))) (cons (VarDecl (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12)))))))))))) (cons ((PassThunkRec,Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (1)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (4))) (cons (VarDecl (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (cons (VarDecl (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (nil))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (11)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (13))) (cons (VarDecl (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11)))))) (nil)))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (74))) (cons (VarDecl (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (nil)) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12)))))))))))) (cons ((PassFloatTerm,Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (74))) (cons (VarDecl (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (1)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (4))) (cons (VarDecl (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (cons (VarDecl (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (nil))))) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (11)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (13))) (cons (VarDecl (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11)))))) (nil)))) (nil))))) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12))))))))) (cons ((PassLetNonStrict,Let (NonRec) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base)) (nil) (Name ("EndDate_match") (Unique (74))) (cons (VarDecl (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))))) (cons (VarDecl (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (nil))))) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Bool") (Unique (1)))) (Kind_Base)) (nil) (Name ("Bool_match") (Unique (4))) (cons (VarDecl (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (cons (VarDecl (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (nil))))) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (cons (DatatypeBind (Datatype (TyVarDecl (TyName (Name ("Unit") (Unique (11)))) (Kind_Base)) (nil) (Name ("Unit_match") (Unique (13))) (cons (VarDecl (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11)))))) (nil)))) (nil))))) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12))))))))) (cons ((PassLetTypes,Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base) (LamAbs (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (LamAbs (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("EndDate_match") (Unique (74))) (Ty_Fun (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))))))) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (1)))) (Kind_Base) (LamAbs (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("Bool_match") (Unique (4))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (Apply (Apply (TyInst (TyAbs (TyName (Name ("Unit") (Unique (11)))) (Kind_Base) (LamAbs (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (LamAbs (Name ("Unit_match") (Unique (13))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198)))))))) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12)))))))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198)))))))) (TyAbs (TyName (Name ("out_Unit") (Unique (199)))) (Kind_Base) (LamAbs (Name ("case_Unit") (Unique (200))) (Ty_Var (TyName (Name ("out_Unit") (Unique (199))))) (Var (Name ("case_Unit") (Unique (200))))))) (LamAbs (Name ("x") (Unique (201))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))))) (Var (Name ("x") (Unique (201))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (203)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (204))) (Ty_Var (TyName (Name ("out_Bool") (Unique (203))))) (LamAbs (Name ("case_False") (Unique (205))) (Ty_Var (TyName (Name ("out_Bool") (Unique (203))))) (Var (Name ("case_True") (Unique (204)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (206)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (207))) (Ty_Var (TyName (Name ("out_Bool") (Unique (206))))) (LamAbs (Name ("case_False") (Unique (208))) (Ty_Var (TyName (Name ("out_Bool") (Unique (206))))) (Var (Name ("case_False") (Unique (208)))))))) (LamAbs (Name ("x") (Unique (209))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202)))))))) (Var (Name ("x") (Unique (209)))))))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))))))) (LamAbs (Name ("arg_0") (Unique (214))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (TyAbs (TyName (Name ("out_EndDate") (Unique (211)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (212))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (211)))))) (LamAbs (Name ("case_Never") (Unique (213))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (211))))) (Apply (Var (Name ("case_Fixed") (Unique (212)))) (Var (Name ("arg_0") (Unique (214)))))))))) (TyAbs (TyName (Name ("out_EndDate") (Unique (215)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (216))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (215)))))) (LamAbs (Name ("case_Never") (Unique (217))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (215))))) (Var (Name ("case_Never") (Unique (217)))))))) (LamAbs (Name ("x") (Unique (218))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))))) (Var (Name ("x") (Unique (218))))))) (cons ((PassLetRec,Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("EndDate") (Unique (71)))) (Kind_Base) (LamAbs (Name ("Fixed") (Unique (72))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (71)))))) (LamAbs (Name ("Never") (Unique (73))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("EndDate_match") (Unique (74))) (Ty_Fun (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))))))) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (1)))) (Kind_Base) (LamAbs (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("Bool_match") (Unique (4))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (Apply (Apply (TyInst (TyAbs (TyName (Name ("Unit") (Unique (11)))) (Kind_Base) (LamAbs (Name ("Unit") (Unique (12))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (LamAbs (Name ("Unit_match") (Unique (13))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198)))))))) (LamAbs (Name ("ds") (Unique (75))) (Ty_Var (TyName (Name ("EndDate") (Unique (71))))) (LamAbs (Name ("ds") (Unique (76))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (74)))) (Var (Name ("ds") (Unique (75))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))))) (LamAbs (Name ("n") (Unique (79))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (80))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Var (Name ("n") (Unique (79))))) (Var (Name ("ds") (Unique (76)))))))) (LamAbs (Name ("thunk") (Unique (81))) (Ty_Var (TyName (Name ("Unit") (Unique (11))))) (Var (Name ("False") (Unique (3)))))) (Var (Name ("Unit") (Unique (12)))))))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198)))))))) (TyAbs (TyName (Name ("out_Unit") (Unique (199)))) (Kind_Base) (LamAbs (Name ("case_Unit") (Unique (200))) (Ty_Var (TyName (Name ("out_Unit") (Unique (199))))) (Var (Name ("case_Unit") (Unique (200))))))) (LamAbs (Name ("x") (Unique (201))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (198)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (198))))))) (Var (Name ("x") (Unique (201))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (203)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (204))) (Ty_Var (TyName (Name ("out_Bool") (Unique (203))))) (LamAbs (Name ("case_False") (Unique (205))) (Ty_Var (TyName (Name ("out_Bool") (Unique (203))))) (Var (Name ("case_True") (Unique (204)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (206)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (207))) (Ty_Var (TyName (Name ("out_Bool") (Unique (206))))) (LamAbs (Name ("case_False") (Unique (208))) (Ty_Var (TyName (Name ("out_Bool") (Unique (206))))) (Var (Name ("case_False") (Unique (208)))))))) (LamAbs (Name ("x") (Unique (209))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (202)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (202))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (202)))))))) (Var (Name ("x") (Unique (209)))))))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))))))) (LamAbs (Name ("arg_0") (Unique (214))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (TyAbs (TyName (Name ("out_EndDate") (Unique (211)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (212))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (211)))))) (LamAbs (Name ("case_Never") (Unique (213))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (211))))) (Apply (Var (Name ("case_Fixed") (Unique (212)))) (Var (Name ("arg_0") (Unique (214)))))))))) (TyAbs (TyName (Name ("out_EndDate") (Unique (215)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (216))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (215)))))) (LamAbs (Name ("case_Never") (Unique (217))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (215))))) (Var (Name ("case_Never") (Unique (217)))))))) (LamAbs (Name ("x") (Unique (218))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (210)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (210))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (210)))))))) (Var (Name ("x") (Unique (218))))))) (cons ((PassDeadCode,Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("EndDate") (Unique (0)))) (Kind_Base) (LamAbs (Name ("Fixed") (Unique (1))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (0)))))) (LamAbs (Name ("Never") (Unique (2))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("EndDate_match") (Unique (3))) (Ty_Fun (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))))))) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (5)))) (Kind_Base) (LamAbs (Name ("True") (Unique (6))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("False") (Unique (7))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("Bool_match") (Unique (8))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (9)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (10))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (5)))))))) (LamAbs (Name ("arg") (Unique (11))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (12))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (13))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (5)))))) (Var (Name ("b") (Unique (13))))) (Var (Name ("True") (Unique (6))))) (Var (Name ("False") (Unique (7)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (11))))) (Var (Name ("arg") (Unique (12))))))))) (nil)) (Apply (Apply (TyInst (TyAbs (TyName (Name ("Unit") (Unique (14)))) (Kind_Base) (LamAbs (Name ("Unit") (Unique (15))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (LamAbs (Name ("Unit_match") (Unique (16))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (17)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (17))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (17)))))))) (LamAbs (Name ("ds") (Unique (18))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("ds") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (3)))) (Var (Name ("ds") (Unique (18))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))))) (LamAbs (Name ("n") (Unique (20))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (21))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (10)))) (Var (Name ("n") (Unique (20))))) (Var (Name ("ds") (Unique (19)))))))) (LamAbs (Name ("thunk") (Unique (22))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Var (Name ("False") (Unique (7)))))) (Var (Name ("Unit") (Unique (15)))))))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (23)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (23))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (23)))))))) (TyAbs (TyName (Name ("out_Unit") (Unique (24)))) (Kind_Base) (LamAbs (Name ("case_Unit") (Unique (25))) (Ty_Var (TyName (Name ("out_Unit") (Unique (24))))) (Var (Name ("case_Unit") (Unique (25))))))) (LamAbs (Name ("x") (Unique (26))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (27)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))))) (Var (Name ("x") (Unique (26))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (28)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (29)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (30))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (LamAbs (Name ("case_False") (Unique (31))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (Var (Name ("case_True") (Unique (30)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (32)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (33))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (LamAbs (Name ("case_False") (Unique (34))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (Var (Name ("case_False") (Unique (34)))))))) (LamAbs (Name ("x") (Unique (35))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (36)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (36)))))))) (Var (Name ("x") (Unique (35)))))))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (37)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))))))) (LamAbs (Name ("arg_0") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (TyAbs (TyName (Name ("out_EndDate") (Unique (39)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39)))))) (LamAbs (Name ("case_Never") (Unique (41))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39))))) (Apply (Var (Name ("case_Fixed") (Unique (40)))) (Var (Name ("arg_0") (Unique (38)))))))))) (TyAbs (TyName (Name ("out_EndDate") (Unique (42)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (43))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42)))))) (LamAbs (Name ("case_Never") (Unique (44))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42))))) (Var (Name ("case_Never") (Unique (44)))))))) (LamAbs (Name ("x") (Unique (45))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (46)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (46))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))))) (Var (Name ("x") (Unique (45))))))) (cons ((PassInline (nil),Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("EndDate") (Unique (0)))) (Kind_Base) (LamAbs (Name ("Fixed") (Unique (1))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (0)))))) (LamAbs (Name ("Never") (Unique (2))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("EndDate_match") (Unique (3))) (Ty_Fun (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))))))) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (5)))) (Kind_Base) (LamAbs (Name ("True") (Unique (6))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("False") (Unique (7))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("Bool_match") (Unique (8))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (9)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (10))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (5)))))))) (LamAbs (Name ("arg") (Unique (11))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (12))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (13))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (5)))))) (Var (Name ("b") (Unique (13))))) (Var (Name ("True") (Unique (6))))) (Var (Name ("False") (Unique (7)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (11))))) (Var (Name ("arg") (Unique (12))))))))) (nil)) (Apply (Apply (TyInst (TyAbs (TyName (Name ("Unit") (Unique (14)))) (Kind_Base) (LamAbs (Name ("Unit") (Unique (15))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (LamAbs (Name ("Unit_match") (Unique (16))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (17)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (17))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (17)))))))) (LamAbs (Name ("ds") (Unique (18))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("ds") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (3)))) (Var (Name ("ds") (Unique (18))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))))) (LamAbs (Name ("n") (Unique (20))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (21))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (10)))) (Var (Name ("n") (Unique (20))))) (Var (Name ("ds") (Unique (19)))))))) (LamAbs (Name ("thunk") (Unique (22))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Var (Name ("False") (Unique (7)))))) (Var (Name ("Unit") (Unique (15)))))))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (23)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (23))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (23)))))))) (TyAbs (TyName (Name ("out_Unit") (Unique (24)))) (Kind_Base) (LamAbs (Name ("case_Unit") (Unique (25))) (Ty_Var (TyName (Name ("out_Unit") (Unique (24))))) (Var (Name ("case_Unit") (Unique (25))))))) (LamAbs (Name ("x") (Unique (26))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (27)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))))) (Var (Name ("x") (Unique (26))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (28)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (29)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (30))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (LamAbs (Name ("case_False") (Unique (31))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (Var (Name ("case_True") (Unique (30)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (32)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (33))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (LamAbs (Name ("case_False") (Unique (34))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (Var (Name ("case_False") (Unique (34)))))))) (LamAbs (Name ("x") (Unique (35))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (36)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (36)))))))) (Var (Name ("x") (Unique (35)))))))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (37)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))))))) (LamAbs (Name ("arg_0") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (TyAbs (TyName (Name ("out_EndDate") (Unique (39)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39)))))) (LamAbs (Name ("case_Never") (Unique (41))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39))))) (Apply (Var (Name ("case_Fixed") (Unique (40)))) (Var (Name ("arg_0") (Unique (38)))))))))) (TyAbs (TyName (Name ("out_EndDate") (Unique (42)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (43))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42)))))) (LamAbs (Name ("case_Never") (Unique (44))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42))))) (Var (Name ("case_Never") (Unique (44)))))))) (LamAbs (Name ("x") (Unique (45))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (46)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (46))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))))) (Var (Name ("x") (Unique (45))))))) (cons ((PassLetNonRec,Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("EndDate") (Unique (0)))) (Kind_Base) (LamAbs (Name ("Fixed") (Unique (1))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("EndDate") (Unique (0)))))) (LamAbs (Name ("Never") (Unique (2))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("EndDate_match") (Unique (3))) (Ty_Fun (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (4))))))))) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (5)))) (Kind_Base) (LamAbs (Name ("True") (Unique (6))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("False") (Unique (7))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (LamAbs (Name ("Bool_match") (Unique (8))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (5))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (9)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (9))))))))) (Apply (LamAbs (Name ("lessThanEqInteger") (Unique (10))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))))) (Apply (Apply (TyInst (TyAbs (TyName (Name ("Unit") (Unique (14)))) (Kind_Base) (LamAbs (Name ("Unit") (Unique (15))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (LamAbs (Name ("Unit_match") (Unique (16))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (17)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (17))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (17)))))))) (LamAbs (Name ("ds") (Unique (18))) (Ty_Var (TyName (Name ("EndDate") (Unique (0))))) (LamAbs (Name ("ds") (Unique (19))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (Apply (Apply (TyInst (Apply (Var (Name ("EndDate_match") (Unique (3)))) (Var (Name ("ds") (Unique (18))))) (Ty_Fun (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Ty_Var (TyName (Name ("Bool") (Unique (5))))))) (LamAbs (Name ("n") (Unique (20))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("thunk") (Unique (21))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (10)))) (Var (Name ("n") (Unique (20))))) (Var (Name ("ds") (Unique (19)))))))) (LamAbs (Name ("thunk") (Unique (22))) (Ty_Var (TyName (Name ("Unit") (Unique (14))))) (Var (Name ("False") (Unique (7)))))) (Var (Name ("Unit") (Unique (15)))))))))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (23)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (23))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (23)))))))) (TyAbs (TyName (Name ("out_Unit") (Unique (24)))) (Kind_Base) (LamAbs (Name ("case_Unit") (Unique (25))) (Ty_Var (TyName (Name ("out_Unit") (Unique (24))))) (Var (Name ("case_Unit") (Unique (25))))))) (LamAbs (Name ("x") (Unique (26))) (Ty_Forall (TyName (Name ("out_Unit") (Unique (27)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))) (Ty_Var (TyName (Name ("out_Unit") (Unique (27))))))) (Var (Name ("x") (Unique (26))))))) (LamAbs (Name ("arg") (Unique (11))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (12))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (13))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (5)))))) (Var (Name ("b") (Unique (13))))) (Var (Name ("True") (Unique (6))))) (Var (Name ("False") (Unique (7)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (11))))) (Var (Name ("arg") (Unique (12))))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (28)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (28))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (29)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (30))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (LamAbs (Name ("case_False") (Unique (31))) (Ty_Var (TyName (Name ("out_Bool") (Unique (29))))) (Var (Name ("case_True") (Unique (30)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (32)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (33))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (LamAbs (Name ("case_False") (Unique (34))) (Ty_Var (TyName (Name ("out_Bool") (Unique (32))))) (Var (Name ("case_False") (Unique (34)))))))) (LamAbs (Name ("x") (Unique (35))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (36)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (36))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (36)))))))) (Var (Name ("x") (Unique (35)))))))))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (37)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (37))))))))) (LamAbs (Name ("arg_0") (Unique (38))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (TyAbs (TyName (Name ("out_EndDate") (Unique (39)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (40))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39)))))) (LamAbs (Name ("case_Never") (Unique (41))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (39))))) (Apply (Var (Name ("case_Fixed") (Unique (40)))) (Var (Name ("arg_0") (Unique (38)))))))))) (TyAbs (TyName (Name ("out_EndDate") (Unique (42)))) (Kind_Base) (LamAbs (Name ("case_Fixed") (Unique (43))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42)))))) (LamAbs (Name ("case_Never") (Unique (44))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (42))))) (Var (Name ("case_Never") (Unique (44)))))))) (LamAbs (Name ("x") (Unique (45))) (Ty_Forall (TyName (Name ("out_EndDate") (Unique (46)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))) (Ty_Fun (Ty_Var (TyName (Name ("out_EndDate") (Unique (46))))) (Ty_Var (TyName (Name ("out_EndDate") (Unique (46)))))))) (Var (Name ("x") (Unique (45))))))) (nil))))))))))))).




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
  | IfThenElse => Ty_Forall "a" Kind_Base (Ty_Fun Ty_Bool (Ty_Fun (Ty_Var "a") (Ty_Var "a")))
  | CharToString => Ty_Fun Ty_Char Ty_String
  | Append => Ty_Fun Ty_String (Ty_Fun Ty_String Ty_String)
  | Trace => Ty_Fun Ty_String Ty_Unit (* TODO: figure out if it is the correct type*)
  end.

(** Typing of terms *)
(* TODO: Should I include normalisation in type rules? They are not type directed at the moment. *)
Reserved Notation "ctx '|-' tm ':' T" (at level 40, tm at level 0, T at level 0).
Inductive has_type : Context -> Term -> Ty -> Prop :=
  (* TODO : Let-bindings *)
  (* 
  | T_Let 
  *)
  (* Basic constructs *)
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
      ctx |- (Constant (Some (ValueOf u type))) : (Ty_Builtin (Some (TypeIn u))) (* TODO *)
  | T_Builtin : forall ctx f,
      ctx |- (Builtin f) : (lookupBuiltinTy f)
  | T_TyInst : forall ctx t1 T2 T1 X K2,
      ctx |- t1 : (Ty_Forall X K2 T1) ->
      ctx |-* T2 : K2 ->
      ctx |- (TyInst t1 T2) : (substituteT X T2 T1)
  | T_Error : forall ctx T,
      ctx |-* T : Kind_Base ->
      ctx |- (Error T) : T 
  (* Recursive types *)
  | T_IWrap : forall ctx F T M X K,
      ctx |- M : (Ty_App (Ty_App F (Ty_Lam X K (Ty_IFix F (Ty_Var X)))) T) ->
      ctx |-* T : K ->
      ctx |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      ctx |- (IWrap F T M) : (Ty_IFix F T)
  | T_Unwrap : forall ctx M F X K T,
      ctx |- M : (Ty_IFix F T) ->
      ctx |-* T : K ->
      ctx |- (Unwrap M) : (Ty_App (Ty_App F (Ty_Lam X K (Ty_IFix F (Ty_Var X)))) T)
  (* Type equality *)
  | T_Eq : forall ctx t T S,
      ctx |- t : S ->
      S =b T ->
      ctx |- t : T
where "ctx '|-' tm ':' T" := (has_type ctx tm T).

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


