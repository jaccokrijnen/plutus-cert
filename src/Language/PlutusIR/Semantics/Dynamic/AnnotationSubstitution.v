Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.

(** * Substitution of types in type annotations *)

(** ** Utilities *)
Definition tyvars_bound_by_binding (b : NamedTerm.Binding) : list tyname :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition tyvars_bound_by_bindings (bs : list NamedTerm.Binding) : list tyname := List.concat (map tyvars_bound_by_binding bs).

(** ** Implementation as an inductive datatype *)
Definition substituteA_constructor (X : tyname) (S : Ty) (c : constructor) : constructor :=
  match c with
  | Constructor (VarDecl x T) ar => Constructor (VarDecl x (substituteT X S T)) ar
  end.

Inductive substituteA : tyname -> Ty -> Term -> Term -> Prop :=
  | SA_Let1 : forall X S bs t0 bs',
      In X (tyvars_bound_by_bindings bs) ->
      substituteA_bindings_nonrec X S bs bs' ->
      substituteA X S (Let NonRec bs t0) (Let NonRec bs' t0)
  | SA_Let2 : forall X S bs t0 bs' t0',
      ~(In X (tyvars_bound_by_bindings bs)) ->
      substituteA_bindings_nonrec X S bs bs' ->
      substituteA X S t0 t0' ->
      substituteA X S (Let NonRec bs t0) (Let NonRec bs' t0')
  | SA_LetRec1 : forall X S bs t0,
      In X (tyvars_bound_by_bindings bs)->
      substituteA X S (Let Rec bs t0) (Let Rec bs t0)
  | SA_LetRec2 : forall X S bs t0 bs' t0',
      ~(In X (tyvars_bound_by_bindings bs)) ->
      substituteA_bindings_rec X S bs bs' ->
      substituteA X S t0 t0' ->
      substituteA X S (Let Rec bs t0) (Let Rec bs' t0')
  | SA_Var : forall X S x,
      substituteA X S (Var x) (Var x)
  | SA_TyAbs1 : forall X S K t0,
      substituteA X S (TyAbs X K t0) (TyAbs X K t0)
  | SA_TyAbs2 : forall X S bX K t0 t0',
      X <> bX ->
      substituteA X S t0 t0' ->
      substituteA X S (TyAbs bX K t0) (TyAbs bX K t0')
  | SA_LamAbs : forall X S bx T t0 t0',
      substituteA X S t0 t0' ->
      substituteA X S (LamAbs bx T t0) (LamAbs bx (substituteT X S T) t0')
  | SA_Apply : forall X S t1 t2 t1' t2',
      substituteA X S t1 t1' ->
      substituteA X S t2 t2' ->
      substituteA X S (Apply t1 t2) (Apply t1' t2')
  | SA_Constant : forall X S u,
      substituteA X S (Constant u) (Constant u)
  | SA_Builtin : forall X S d,
      substituteA X S (Builtin d) (Builtin d)
  | SA_TyInst : forall X S t0 T t0',
      substituteA X S t0 t0' ->
      substituteA X S (TyInst t0 T) (TyInst t0' (substituteT X S T))
  | SA_Error : forall X S T,
      substituteA X S (Error T) (Error (substituteT X S T))
  | SA_IWrap : forall X S F T t0 t0',
      substituteA X S t0 t0' ->
      substituteA X S (IWrap F T t0) (IWrap (substituteT X S F) (substituteT X S T) t0')
  | SA_Unwrap : forall X S t0 t0',
      substituteA X S t0 t0' ->
      substituteA X S (Unwrap t0) (Unwrap t0') 
      
with substituteA_bindings_nonrec : tyname -> Ty -> list Binding -> list Binding -> Prop :=
  | SA_NilB_NonRec : forall X S, 
      substituteA_bindings_nonrec X S nil nil
  | SA_ConsB_NonRec1 : forall X S b b' bs,
      In X (tyvars_bound_by_binding b) ->
      substituteA_binding X S b b' ->
      substituteA_bindings_nonrec X S (b :: bs) (b' :: bs)
  | SA_ConsB_NonRec2 : forall X S b b' bs bs',
      ~(In X (tyvars_bound_by_binding b)) ->
      substituteA_binding X S b b' ->
      substituteA_bindings_nonrec X S bs bs' ->
      substituteA_bindings_nonrec X S (b :: bs) (b' :: bs')

with substituteA_bindings_rec : tyname -> Ty -> list Binding -> list Binding -> Prop :=
  | SA_NilB_Rec : forall X S,
      substituteA_bindings_rec X S nil nil
  | SA_ConsB_Rec : forall X S b b' bs bs',
      substituteA_binding X S b b' ->
      substituteA_bindings_rec X S bs bs' ->
      substituteA_bindings_rec X S (b :: bs) (b' :: bs')

with substituteA_binding : tyname -> Ty -> Binding -> Binding -> Prop :=
  | SA_TermBind : forall X S strictness bx T t t',
      substituteA X S t t' ->
      substituteA_binding X S (TermBind strictness (VarDecl bx T) t) (TermBind strictness (VarDecl bx (substituteT X S T)) t')
  | SA_TypeBind : forall X S tvd T,
      substituteA_binding X S (TypeBind tvd T) (TypeBind tvd (substituteT X S T))
  | SA_DatatypeBind : forall X S tvd YKs matchFunc cs,
      substituteA_binding X S (DatatypeBind (Datatype tvd YKs matchFunc cs)) (DatatypeBind (Datatype tvd YKs matchFunc (map (substituteA_constructor X S) cs))).

#[export] Hint Constructors substituteA : core.
#[export] Hint Constructors substituteA_bindings_nonrec : core.
#[export] Hint Constructors substituteA_bindings_rec : core.
#[export] Hint Constructors substituteA_binding : core.

Scheme substituteA__ind := Minimality for substituteA Sort Prop
  with substituteA_bindings_nonrec__ind := Minimality for substituteA_bindings_nonrec Sort Prop
  with substituteA_bindings_rec__ind := Minimality for substituteA_bindings_rec Sort Prop
  with substituteA_binding__ind := Minimality for substituteA_binding Sort Prop.

Combined Scheme substituteA__mutind from 
  substituteA__ind, 
  substituteA_bindings_nonrec__ind, 
  substituteA_bindings_rec__ind, 
  substituteA_binding__ind.



(** * Multi-substitutions of types in type annotations *)

Definition envA := list (tyname * Ty).

Inductive msubstA : envA -> Term -> Term -> Prop :=
  | msubstA_nil : forall t,
      msubstA nil t t
  | msubstA_cons : forall a T ss t t' t'',
      substituteA a T t t' ->
      msubstA ss t' t'' ->
      msubstA ((a, T) :: ss) t t''
  .