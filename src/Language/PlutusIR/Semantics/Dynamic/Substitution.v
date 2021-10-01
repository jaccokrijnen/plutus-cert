Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** * Substitution of terms *)

(** ** Utilities *)
Definition bound_var_in_constructor (c : NamedTerm.constructor) : string :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition bound_var_in_binding (b : NamedTerm.Binding) : list string :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map bound_var_in_constructor cs))
  end.

Definition bound_vars_in_bindings (bs : list NamedTerm.Binding) : list string := List.concat (map bound_var_in_binding bs).

(** ** Implementation of substitution on terms as inductive datatype *)
Inductive substitute (x : name) (s : Term) :Term -> Term -> Prop :=
  | S_LetNonRec_Nil1 : forall t t', 
      substitute x s t t' ->
      substitute x s (Let NonRec nil t) (Let NonRec nil t')
  | S_LetNonRec_Cons1 : forall b b' bs t,
      In x (bound_var_in_binding b) ->
      substitute_binding x s b b' ->
      substitute x s (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs) t)
  | S_LetNonRec_Cons2 : forall b b' bs bs' t t',
      ~(In x (bound_var_in_binding b)) ->
      substitute_binding x s b b' ->
      substitute x s (Let NonRec bs t) (Let NonRec bs' t') ->
      substitute x s (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')
  | S_LetRec1 : forall bs t0,
      In x (bound_vars_in_bindings bs)->
      substitute x s (Let Rec bs t0) (Let Rec bs t0)
  | S_LetRec2 : forall bs t0 bs' t0',
      ~(In x (bound_vars_in_bindings bs)) ->
      substitute_letrec x s (Let Rec bs t0) (Let Rec bs' t0') ->
      substitute x s (Let Rec bs t0) (Let Rec bs' t0')
  | S_Var1 :
      substitute x s (Var x) s
  | S_Var2 : forall y,
      x <> y ->
      substitute x s (Var y) (Var y)
  | S_TyAbs : forall bX K t0 t0',
      substitute x s t0 t0' ->
      substitute x s (TyAbs bX K t0) (TyAbs bX K t0')
  | S_LamAbs1 : forall T t0,
      substitute x s (LamAbs x T t0) (LamAbs x T t0)
  | S_LamAbs2 : forall bx T t0 t0',
      x <> bx ->
      substitute x s t0 t0' ->
      substitute x s (LamAbs bx T t0) (LamAbs bx T t0') 
  | S_Apply : forall t1 t2 t1' t2',
      substitute x s t1 t1' ->
      substitute x s t2 t2' ->
      substitute x s (Apply t1 t2) (Apply t1' t2')
  | S_Constant : forall u,
      substitute x s (Constant u) (Constant u)
  | S_Builtin : forall d,
      substitute x s (Builtin d) (Builtin d)
  | S_TyInst : forall t0 T t0',
      substitute x s t0 t0' ->
      substitute x s (TyInst t0 T) (TyInst t0' T)
  | S_Error : forall T,
      substitute x s (Error T) (Error T)
  | S_IWrap : forall F T t0 t0',
      substitute x s t0 t0' ->
      substitute x s (IWrap F T t0) (IWrap F T t0')
  | S_Unwrap : forall t0 t0',
      substitute x s t0 t0' ->
      substitute x s (Unwrap t0) (Unwrap t0') 

with substitute_letrec (x : name) (s : Term) : Term -> Term -> Prop :=
  | S_NilB_Rec : forall t t',
      substitute x s t t' ->
      substitute_letrec x s (Let Rec nil t) (Let Rec nil t')
  | S_ConsB_Rec : forall b b' bs bs' t t',
      substitute_binding x s b b' ->
      substitute_letrec x s (Let Rec bs t) (Let Rec bs' t') ->
      substitute_letrec x s (Let Rec (b :: bs) t) (Let Rec (b' :: bs') t')

with substitute_binding (x : name) (s : Term) : Binding -> Binding -> Prop :=
  | S_TermBind : forall strictness bx T t t',
      substitute x s t t' ->
      substitute_binding x s (TermBind strictness (VarDecl bx T) t) (TermBind strictness (VarDecl bx T) t')
  | S_TypeBind : forall tvd T,
      substitute_binding x s (TypeBind tvd T) (TypeBind tvd T)
  | S_DatatypeBind : forall dtd,
      substitute_binding x s (DatatypeBind dtd) (DatatypeBind dtd).

#[export] Hint Constructors substitute : core.
#[export] Hint Constructors substitute_letrec : core.
#[export] Hint Constructors substitute_binding : core.

Scheme substitute__ind := Minimality for substitute Sort Prop
  with substitute_letrec__ind := Minimality for substitute_letrec Sort Prop
  with substitute_binding__ind := Minimality for substitute_binding Sort Prop.

Combined Scheme substitute__mutind from 
  substitute__ind, 
  substitute_letrec__ind, 
  substitute_binding__ind.

(** * Multi-substitutions of types in type annotations *)

Definition env := list (name * Term).

Inductive msubst_term : env -> Term -> Term -> Prop :=
  | msubst_term__nil : forall t,
      msubst_term nil t t
  | msubst_term__cons : forall x s ss t t' t'',
      substitute x s t t' ->
      msubst_term ss t' t'' ->
      msubst_term ((x, s) :: ss) t t''
  .

Inductive msubst_binding : env -> Binding -> Binding -> Prop :=
  | msubst_binding__nil : forall b,
      msubst_binding nil b b
  | msubst_binding__cons : forall x s ss b b' b'',
      substitute_binding x s b b' ->
      msubst_binding ss b' b'' ->
      msubst_binding ((x, s) :: ss) b b''.