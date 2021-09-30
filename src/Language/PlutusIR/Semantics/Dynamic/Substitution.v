Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** * Substitution of terms *)

(** ** Utilities *)
Definition term_var_bound_by_constructor (c : NamedTerm.constructor) : string :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition term_vars_bound_by_binding (b : NamedTerm.Binding) : list string :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map term_var_bound_by_constructor cs))
  end.

Definition term_vars_bound_by_bindings (bs : list NamedTerm.Binding) : list string := List.concat (map term_vars_bound_by_binding bs).

(** ** Implementation of substitution on terms as inductive datatype *)
Inductive substitute : name -> Term -> Term -> Term -> Prop :=
  | S_Let1 : forall x s bs t0 bs',
      In x (term_vars_bound_by_bindings bs) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0)
  | S_Let2 : forall x s bs t0 bs' t0',
      ~(In x (term_vars_bound_by_bindings bs)) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0')
  | S_LetRec1 : forall x s bs t0,
      In x (term_vars_bound_by_bindings bs)->
      substitute x s (Let Rec bs t0) (Let Rec bs t0)
  | S_LetRec2 : forall x s bs t0 bs' t0',
      ~(In x (term_vars_bound_by_bindings bs)) ->
      substitute_bindings_rec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let Rec bs t0) (Let Rec bs' t0')
  | S_Var1 : forall x s,
      substitute x s (Var x) s
  | S_Var2 : forall x s y,
      x <> y ->
      substitute x s (Var y) (Var y)
  | S_TyAbs : forall x s bX K t0 t0',
      substitute x s t0 t0' ->
      substitute x s (TyAbs bX K t0) (TyAbs bX K t0')
  | S_LamAbs1 : forall x s T t0,
      substitute x s (LamAbs x T t0) (LamAbs x T t0)
  | S_LamAbs2 : forall x s bx T t0 t0',
      x <> bx ->
      substitute x s t0 t0' ->
      substitute x s (LamAbs bx T t0) (LamAbs bx T t0') 
  | S_Apply : forall x s t1 t2 t1' t2',
      substitute x s t1 t1' ->
      substitute x s t2 t2' ->
      substitute x s (Apply t1 t2) (Apply t1' t2')
  | S_Constant : forall x s u,
      substitute x s (Constant u) (Constant u)
  | S_Builtin : forall x s d,
      substitute x s (Builtin d) (Builtin d)
  | S_TyInst : forall x s t0 T t0',
      substitute x s t0 t0' ->
      substitute x s (TyInst t0 T) (TyInst t0' T)
  | S_Error : forall x s T,
      substitute x s (Error T) (Error T)
  | S_IWrap : forall x s F T t0 t0',
      substitute x s t0 t0' ->
      substitute x s (IWrap F T t0) (IWrap F T t0')
  | S_Unwrap : forall x s t0 t0',
      substitute x s t0 t0' ->
      substitute x s (Unwrap t0) (Unwrap t0') 
      
with substitute_bindings_nonrec : name -> Term -> list Binding -> list Binding -> Prop :=
  | S_NilB_NonRec : forall x s, 
      substitute_bindings_nonrec x s nil nil
  | S_ConsB_NonRec1 : forall x s b b' bs,
      In x (term_vars_bound_by_binding b) ->
      substitute_binding x s b b' ->
      substitute_bindings_nonrec x s (b :: bs) (b' :: bs)
  | S_ConsB_NonRec2 : forall x s b b' bs bs',
      ~(In x (term_vars_bound_by_binding b)) ->
      substitute_binding x s b b' ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute_bindings_nonrec x s (b :: bs) (b' :: bs')

with substitute_bindings_rec : name -> Term -> list Binding -> list Binding -> Prop :=
  | S_NilB_Rec : forall x s,
      substitute_bindings_rec x s nil nil
  | S_ConsB_Rec : forall x s b b' bs bs',
      substitute_binding x s b b' ->
      substitute_bindings_rec x s bs bs' ->
      substitute_bindings_rec x s (b :: bs) (b' :: bs')

with substitute_binding : name -> Term -> Binding -> Binding -> Prop :=
  | S_TermBind : forall x s strictness bx T t t',
      substitute x s t t' ->
      substitute_binding x s (TermBind strictness (VarDecl bx T) t) (TermBind strictness (VarDecl bx T) t')
  | S_TypeBind : forall x s tvd T,
      substitute_binding x s (TypeBind tvd T) (TypeBind tvd T)
  | S_DatatypeBind : forall x s dtd,
      substitute_binding x s (DatatypeBind dtd) (DatatypeBind dtd).

#[export] Hint Constructors substitute : core.
#[export] Hint Constructors substitute_bindings_nonrec : core.
#[export] Hint Constructors substitute_bindings_rec : core.
#[export] Hint Constructors substitute_binding : core.

Scheme substitute__ind := Minimality for substitute Sort Prop
  with substitute_bindings_nonrec__ind := Minimality for substitute_bindings_nonrec Sort Prop
  with substitute_bindings_rec__ind := Minimality for substitute_bindings_rec Sort Prop
  with substitute_binding__ind := Minimality for substitute_binding Sort Prop.

Combined Scheme substitute__mutind from 
  substitute__ind, 
  substitute_bindings_nonrec__ind, 
  substitute_bindings_rec__ind, 
  substitute_binding__ind.



(** * Multi-substitutions of types in type annotations *)

Definition env := list (name * Term).

Inductive msubst : env -> Term -> Term -> Prop :=
  | msubst_nil : forall t,
      msubst nil t t
  | msubst_cons : forall x s ss t t' t'',
      substitute x s t t' ->
      msubst ss t' t'' ->
      msubst ((x, s) :: ss) t t''
  .

Inductive msubst_binding : env -> Binding -> Binding -> Prop :=
  | msubst_binding__nil : forall b,
      msubst_binding nil b b
  | msubst_binding__cons : forall x s ss b b' b'',
      substitute_binding x s b b' ->
      msubst_binding ss b' b'' ->
      msubst_binding ((x, s) :: ss) b b''.