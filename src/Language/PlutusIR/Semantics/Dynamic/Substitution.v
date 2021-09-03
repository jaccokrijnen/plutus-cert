Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



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





(** * Substitution of types in type annotations on the term level *)

(** ** Utilities *)
Definition tyvars_bound_by_binding (b : NamedTerm.Binding) : list tyname :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition tyvars_bound_by_bindings (bs : list NamedTerm.Binding) : list tyname := List.concat (map tyvars_bound_by_binding bs).

(** ** Implementation as an inductive datatype *)
Definition annotsubst_constructor (X : tyname) (S : Ty) (c : constructor) : constructor :=
  match c with
  | Constructor (VarDecl x T) ar => Constructor (VarDecl x (substituteT X S T)) ar
  end.

Inductive annotsubst : tyname -> Ty -> Term -> Term -> Prop :=
  | SA_Let1 : forall X S bs t0 bs',
      In X (tyvars_bound_by_bindings bs) ->
      annotsubst_bindings_nonrec X S bs bs' ->
      annotsubst X S (Let NonRec bs t0) (Let NonRec bs' t0)
  | SA_Let2 : forall X S bs t0 bs' t0',
      ~(In X (tyvars_bound_by_bindings bs)) ->
      annotsubst_bindings_nonrec X S bs bs' ->
      annotsubst X S t0 t0' ->
      annotsubst X S (Let NonRec bs t0) (Let NonRec bs' t0')
  | SA_LetRec1 : forall X S bs t0,
      In X (tyvars_bound_by_bindings bs)->
      annotsubst X S (Let Rec bs t0) (Let Rec bs t0)
  | SA_LetRec2 : forall X S bs t0 bs' t0',
      ~(In X (tyvars_bound_by_bindings bs)) ->
      annotsubst_bindings_rec X S bs bs' ->
      annotsubst X S t0 t0' ->
      annotsubst X S (Let Rec bs t0) (Let Rec bs' t0')
  | SA_Var : forall X S x,
      annotsubst X S (Var x) (Var x)
  | SA_TyAbs1 : forall X S K t0 t0',
      annotsubst X S (TyAbs X K t0) (TyAbs X K t0')
  | SA_TyAbs2 : forall X S bX K t0 t0',
      X <> bX ->
      annotsubst X S t0 t0' ->
      annotsubst X S (TyAbs bX K t0) (TyAbs bX K t0')
  | SA_LamAbs : forall X S bx T t0 t0',
      annotsubst X S t0 t0' ->
      annotsubst X S (LamAbs bx T t0) (LamAbs bx (beta_reduce (substituteT X S T)) t0')
  | SA_Apply : forall X S t1 t2 t1' t2',
      annotsubst X S t1 t1' ->
      annotsubst X S t2 t2' ->
      annotsubst X S (Apply t1 t2) (Apply t1' t2')
  | SA_Constant : forall X S u,
      annotsubst X S (Constant u) (Constant u)
  | SA_Builtin : forall X S d,
      annotsubst X S (Builtin d) (Builtin d)
  | SA_TyInst : forall X S t0 T t0',
      annotsubst X S t0 t0' ->
      annotsubst X S (TyInst t0 T) (TyInst t0' (beta_reduce (substituteT X S T)))
  | SA_Error : forall X S T,
      annotsubst X S (Error T) (Error T)
  | SA_IWrap : forall X S F T t0 t0',
      annotsubst X S t0 t0' ->
      annotsubst X S (IWrap F T t0) (IWrap F T t0')
  | SA_Unwrap : forall X S t0 t0',
      annotsubst X S t0 t0' ->
      annotsubst X S (Unwrap t0) (Unwrap t0') 
      
with annotsubst_bindings_nonrec : tyname -> Ty -> list Binding -> list Binding -> Prop :=
  | SA_NilB_NonRec : forall X S, 
      annotsubst_bindings_nonrec X S nil nil
  | SA_ConsB_NonRec1 : forall X S b b' bs,
      In X (term_vars_bound_by_binding b) ->
      annotsubst_binding X S b b' ->
      annotsubst_bindings_nonrec X S (b :: bs) (b' :: bs)
  | SA_ConsB_NonRec2 : forall X S b b' bs bs',
      ~(In X (term_vars_bound_by_binding b)) ->
      annotsubst_binding X S b b' ->
      annotsubst_bindings_nonrec X S bs bs' ->
      annotsubst_bindings_nonrec X S (b :: bs) (b' :: bs')

with annotsubst_bindings_rec : tyname -> Ty -> list Binding -> list Binding -> Prop :=
  | SA_NilB_Rec : forall X S,
      annotsubst_bindings_rec X S nil nil
  | SA_ConsB_Rec : forall X S b b' bs bs',
      annotsubst_binding X S b b' ->
      annotsubst_bindings_rec X S bs bs' ->
      annotsubst_bindings_rec X S (b :: bs) (b' :: bs')

with annotsubst_binding : tyname -> Ty -> Binding -> Binding -> Prop :=
  | SA_TermBind : forall X S strictness bx T t t',
      annotsubst X S t t' ->
      annotsubst_binding X S (TermBind strictness (VarDecl bx T) t) (TermBind strictness (VarDecl bx (beta_reduce (substituteT X S T))) t')
  | SA_TypeBind : forall X S tvd T,
      annotsubst_binding X S (TypeBind tvd T) (TypeBind tvd (beta_reduce (substituteT X S T)))
  | SA_DatatypeBind : forall X S tvd YKs matchFunc cs,
      annotsubst_binding X S (DatatypeBind (Datatype tvd YKs matchFunc cs)) (DatatypeBind (Datatype tvd YKs matchFunc (map (annotsubst_constructor X S) cs))).

#[export] Hint Constructors annotsubst : core.
#[export] Hint Constructors annotsubst_bindings_nonrec : core.
#[export] Hint Constructors annotsubst_bindings_rec : core.
#[export] Hint Constructors annotsubst_binding : core.

Scheme annotsubst__ind := Minimality for annotsubst Sort Prop
  with annotsubst_bindings_nonrec__ind := Minimality for annotsubst_bindings_nonrec Sort Prop
  with annotsubst_bindings_rec__ind := Minimality for annotsubst_bindings_rec Sort Prop
  with annotsubst_binding__ind := Minimality for annotsubst_binding Sort Prop.

Combined Scheme annotsubst__mutind from 
  annotsubst__ind, 
  annotsubst_bindings_nonrec__ind, 
  annotsubst_bindings_rec__ind, 
  annotsubst_binding__ind.