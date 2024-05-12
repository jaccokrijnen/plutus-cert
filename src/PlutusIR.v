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
    | DefaultUniInteger    (* : DefaultUni Z (* Integer *) *)
    | DefaultUniByteString (* : DefaultUni string (* BS.ByteString *)*)
    | DefaultUniString     (* : DefaultUni string (* String *)*)
    | DefaultUniChar       (* : DefaultUni ascii (* Char *)*)
    | DefaultUniUnit       (* : DefaultUni unit (* () *)*)
    | DefaultUniBool       (* : DefaultUni bool (* Bool *)*)
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

(** Constants *)
Definition uniType (x : DefaultUni) : Type :=
  match x with
    | DefaultUniInteger    => Z
    | DefaultUniByteString => string
    | DefaultUniString     => string
    | DefaultUniChar       => ascii
    | DefaultUniUnit       => unit
    | DefaultUniBool       => bool
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

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

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
  | Ty_App : ty -> ty -> ty
  (* | Ty_SOP : list (list ty) -> ty *)
.

(*
  Note [Simplification of AST representation]

  In the Haskell AST, Term is a functor and each constructor may have a field of
  the type parameter `a`. This seems to be used for internal metadata on the
  AST. At the moment we don't use it and don't represent it in the AST.

*)

(** Declarations *)
Inductive vdecl := VarDecl : binderName -> ty -> vdecl.
Inductive tvdecl := TyVarDecl : binderTyname -> kind -> tvdecl.
Inductive dtdecl := Datatype : tvdecl -> list tvdecl -> binderName -> list vdecl -> dtdecl.

(** Terms and bindings *)
(* Perhaps parametrize to mimic original AST in haskell more closely? We really only need one instantiation for now. *)
(* Context {func : Type} {uni : Type -> Type} {name : Type} {tyname : Type}. *)
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


(* AST Helpers *)

Definition vdecl_name : vdecl -> binderName :=
  fun c => match c with
  | VarDecl n _ => n
  end
  .

Definition vdecl_ty : vdecl -> ty :=
  fun c => match c with
  | VarDecl _ ty => ty
  end
  .

Definition tvdecl_name (tvd : tvdecl) : binderTyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

(** * Named terms (all variables and binders are strings) *)

Definition Kind := kind.
Definition Ty := ty.
Definition VDecl := vdecl.
Definition TVDecl := tvdecl.
Definition DTDecl := dtdecl.
Definition Term := term.
Definition Binding := binding.

Definition Context := context.


Section Term_rect.

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

  Fixpoint Term__ind (t : term) : P t :=
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
  with Binding__ind (b : binding) : Q b :=
    match b with
      | TermBind s v t  => H_TermBind s v t (Term__ind t)
      | TypeBind v ty   => H_TypeBind v ty
      | DatatypeBind dtd => H_DatatypeBind dtd
    end.

  Combined Scheme Term__multind from Term__ind, Binding__ind.

End Term__ind.

Section term_rect.
  Variable (P : term -> Type).
  Variable (Q : binding -> Type).
  Variable (R : list binding -> Type).

  Context
    (* (H_Let      : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_Let      : forall rec bs t, R bs -> P t -> P (Let rec bs t))
    (H_Var      : forall s, P (Var s))
    (H_TyAbs    : forall s (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs   : forall s t (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply    : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall s : some valueOf, P (Constant s))
    (H_Builtin  : forall d : DefaultFun, P (Builtin d))
    (H_TyInst   : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error    : forall t : ty, P (Error t))
    (H_IWrap    : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap   : forall t : term, P t -> P (Unwrap t))
    (H_Constr   : forall (i : nat) (ts : list (term)), ForallT P ts -> P (Constr i ts))
    (H_Case    : forall t, P t -> forall ts, ForallT P ts -> P (Case t ts)).

  Context
    (H_TermBind     : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind     : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons         : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil          : R nil).

  Definition bindings_rect' (binding_rect' : forall (b : binding), Q b) :=
    fix bindings_rect' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect' b) (bindings_rect' bs)
    end.

  Definition terms_rect' (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect' (t : term) : P t :=
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
  with binding_rect' (b : binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_rect.

Section ty_fold.

  Context
    {R : Set}.

  Context
    (f_Var : name -> R)
    (f_Fun : R -> R -> R)
    (f_IFix : R -> R -> R)
    (f_Forall :  binderName -> kind -> R -> R)
    (f_Builtin : @some typeIn -> R)
    (f_Lam :  binderName -> kind -> R -> R)
    (f_App : R -> R -> R)
    (f_SOP_prod_cons : R -> R -> R)
    (f_SOP_prod_nil : R)
    (f_SOP_sum_cons : R -> R -> R)
    (f_SOP_sum_nil : R)
    .

  Definition ty_fold := fix fold ty :=
    match ty with
    | Ty_Var v        => f_Var v
    | Ty_Fun t1 t2    => f_Fun (fold t1) (fold t2)
    | Ty_IFix t1 t2   => f_IFix (fold t1) (fold t2)
    | Ty_Forall v k t => f_Forall v k (fold t)
    | Ty_Builtin b    => f_Builtin b
    | Ty_Lam v k t    => f_Lam v k (fold t)
    | Ty_App t1 t2    => f_App (fold t1) (fold t2)
    (*
    | Ty_SOP xs => 
      ((fix f xs := match xs with
        | ys :: xs' =>
          f_SOP_sum_cons
            ((fix g ys :=
              match ys with
              | ty :: ys' => f_SOP_prod_cons (fold ty) (g ys')
              | [] => f_SOP_prod_nil
              end
            ) ys)
            (f xs')
        | [] => f_SOP_sum_nil
      end
      ) xs) *)
    end
.

  Definition ty_alg (ty : ty) : Set := match ty with
    | Ty_Var v        => name -> R
    | Ty_Fun t1 t2    => R -> R -> R
    | Ty_IFix t1 t2   => R -> R -> R
    | Ty_Forall v k t =>  binderName -> kind -> R -> R
    | Ty_Builtin b    => @some typeIn -> R
    | Ty_Lam v k t    =>  binderName -> kind -> R -> R
    | Ty_App t1 t2    => R -> R -> R
    (* | Ty_SOP tys      => (R -> R -> R * R * R -> R -> R * R) *)
    end.

End ty_fold.


Definition ty_endo (m_custom : forall τ, option (@ty_alg ty τ)) := fix f τ :=
  match m_custom τ with
    | Some f_custom => match τ return ty_alg τ -> ty with
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

Definition unitVal : Term := Constant (Some' (ValueOf DefaultUniUnit tt)).



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
