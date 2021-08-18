Require Import PlutusCert.Language.PlutusIR.
Import Coq.Lists.List.
Import Coq.Strings.String.
From Equations Require Import Equations.

Import NamedTerm.

(** * Substitution *)

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

(** ** Implementation of substitution as inductive datatype *)
Inductive substitute : name -> Term -> Term -> Term -> Prop :=
  | S_Let1 : forall x s bs t0 bs',
      (exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0)
  | S_Let2 : forall x s bs t0 bs' t0',
      ~(exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_nonrec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0')
  | S_LetRec1 : forall x s bs t0,
      (exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs t0)
  | S_LetRec2 : forall x s bs t0 bs' t0',
      ~(exists v, In v (term_vars_bound_by_bindings bs) -> x = v) ->
      substitute_bindings_rec x s bs bs' ->
      substitute x s t0 t0' ->
      substitute x s (Let NonRec bs t0) (Let NonRec bs' t0')
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
      (exists v, In v (term_vars_bound_by_binding b) -> x = v) ->
      substitute_binding x s b b' ->
      substitute_bindings_nonrec x s (b :: bs) (b' :: bs)
  | S_ConsB_NonRec2 : forall x s b b' bs bs',
      ~(exists v, In v (term_vars_bound_by_binding b) -> x = v) ->
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

(** ** Definition as a function (failed) *)
Reserved Notation "'[' x '|->' s ']' t" (at level 20).
Fail Equations substitute (x : name) (s t : Term) : Term := {
  substitute x s (Let NonRec bs t0) => 
    if existsb (String.eqb x) (vars_bound_by_bindings bs)
      then Let NonRec (substitute_bindings_nonrec x s bs) t0
      else Let NonRec (substitute_bindings_nonrec x s bs) ([x |-> s] t0) ;
  substitute x s (Let Rec bs t0) => 
    if existsb (String.eqb x) (vars_bound_by_bindings bs)
      then Let Rec bs t0
      else Let Rec bs (*(map (substitute_binding x s) bs)*) ([x |-> s]  t0) ;
  substitute x s (Var y) => 
    if String.eqb x y then s else Var y ;
  substitute x s (TyAbs bX K t0) => 
    TyAbs bX K ([x |-> s]  t0) ;
  substitute x s (LamAbs bx T t0) => 
    if String.eqb x bx
      then LamAbs bx T t0
      else LamAbs bx T ([x |-> s]  t0) ;
  substitute x s (Apply t1 t2) => 
    Apply ([x |-> s]  t1) ([x |-> s]  t2) ;
  substitute x s (Constant u) => 
    Constant u ;
  substitute x s (Builtin d) => 
    Builtin d ;
  substitute x s (TyInst t0 T) => 
    TyInst ([x |-> s]  t0) T ;
  substitute x s (Error T) => 
    Error T ;
  substitute x s (IWrap F T t0) => 
    IWrap F T ([x |-> s]  t0) ;
  substitute x s (Unwrap t0) => 
    Unwrap ([x |-> s]  t0) }
where "'[' x '|->' s ']' t" := (substitute x s t)

with substitute_bindings_nonrec : (x : name) (s : Term) (bs : list Binding) : list Binding := {
  substitute_bindings_nonrec x s nil =>
    nil ;
  substitute_bindings_nonrec x s (TermBind strictness (VarDecl bx T) t :: bs) =>
    if String.eqb x bx
      then TermBind strictness (VarDecl bx T) ([x |-> s] t) :: bs
      else TermBind strictness (VarDecl bx T) ([x |-> s] t) :: substitute_bindings_nonrec x s bs ;
  substitute_bindings_nonrec x s (TypeBind tvd T :: bs) =>
    if existsb (String.eqb x) (vars_bound_by_binding (TypeBind tvd T))
      then TypeBind tvd T :: bs
      else TypeBind tvd T :: substitute_bindings_nonrec x s bs ;
  substitute_bindings_nonrec x s (DatatypeBind dtd :: bs) =>
    if existsb (String.eqb x) (vars_bound_by_binding (DatatypeBind dtd))
      then DatatypeBind dtd :: bs
      else DatatypeBind dtd :: substitute_bindings_nonrec x s bs }.




(** * Big-step operational semantics *)

Inductive value : Term -> Prop :=
  | V_TyAbs : forall bX K t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (TyAbs bX K t0)
  | V_LamAbs : forall bx T t0,
      value (LamAbs bx T t0)
  | V_Constant : forall u,
      value (Constant u)
  | V_Builtin : forall f,
      value (Builtin f)
  | V_Error : forall T,
      value (Error T)
  | V_IWrap : forall F T t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (IWrap F T t0).

(*
Inductive eval : Term -> Term -> Prop :=

with eval_binding : Term -> Term -> Prop.
*)