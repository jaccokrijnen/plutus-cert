Require Import PlutusCert.PlutusIR.
Import PlutusNotations.
Import NamedTerm.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.PlutusIR.Semantics.Dynamic.Values.

Require Import Arith.
Local Open Scope nat_scope.

(** * Big-step operational semantics *)

(** ** Implementation of big-step semantics as an inductive datatype *)
Reserved Notation "t '=[' j ']=>' v"(at level 40).
Reserved Notation "t '=[' j ']=>nr' v"(at level 40).
Reserved Notation "t '=[' j ']=>r' v 'WITH' bs0"(at level 40).

Inductive eval : Term -> Term -> nat -> Prop :=
  | E_LamAbs : forall x T t,
      LamAbs x T t =[0]=> LamAbs x T t
  | E_Apply : forall t1 t2 x T t0 v2 v0 j1 j2 j0,
      t1 =[j1]=> LamAbs x T t0 ->
      t2 =[j2]=> v2 ->
      ~ is_error v2 ->
      <{ [v2 / x] t0 }> =[j0]=> v0 ->
      Apply t1 t2 =[j1 + j2 + 1 + j0]=> v0
  (** Universal types *)
  | E_TyAbs : forall X K t,
      TyAbs X K t =[0]=> TyAbs X K t
  | E_TyInst : forall t1 T2 X K t0 v0 j1 j0,
      t1 =[j1]=> TyAbs X K t0 ->
      <{ [[T2 / X] t0 }> =[j0]=> v0 ->
      TyInst t1 T2 =[j1 + 1 + j0]=> v0
  (** Recursive types *)
  | E_IWrap : forall F T t0 v0 j0,
      t0 =[j0]=> v0 ->
      ~ is_error v0 ->
      IWrap F T t0 =[j0]=> IWrap F T v0
  | E_Unwrap : forall t0 F T v0 j0,
      t0 =[j0]=> IWrap F T v0 ->
      Unwrap t0 =[j0 + 1]=> v0
  (** Constants *)
  | E_Constant : forall a,
      Constant a =[0]=> Constant a
  (** Builtins *)
  | E_Builtin: forall f tys ts v,
      (* TODO: [wip/saturated-builtins] Add eval_terms relation for list of
       * terms to list of values (single step index?) *)
      compute_defaultfun (Builtin f tys ts) = Datatypes.Some v ->
      Builtin f tys ts =[1]=> v
  (* Errors and their propagation *)
  | E_Error : forall T,
      Error T =[0]=> Error T
  | E_Error_Apply1 : forall t1 t2 j1 T,
      t1 =[j1]=> Error T ->
      Apply t1 t2 =[j1 + 1]=> Error T
  | E_Error_Apply2 : forall t1 t2 j2 T,
      t2 =[j2]=> Error T ->
      Apply t1 t2 =[j2 + 1]=> Error T
  | E_Error_TyInst : forall t1 T2 j1 T,
      t1 =[j1]=> Error T ->
      TyInst t1 T2 =[j1 + 1]=> Error T
  | E_Error_IWrap : forall F T t0 j0 T',
      t0 =[j0]=> Error T' ->
      IWrap F T t0 =[j0 + 1]=> Error T'
  | E_Error_Unwrap : forall t0 j0 T,
      t0 =[j0]=> Error T ->
      Unwrap t0 =[j0 + 1]=> Error T

  (* TODO: [wip/saturated-builtins] Add E_Error_Builtin, maybe reuse eval_terms
  * and get the first error? *)

  (** Let-bindings *)
  | E_Let : forall bs t v j,
      Let NonRec bs t =[j]=>nr v ->
      Let NonRec bs t =[j]=> v
  | E_LetRec : forall bs t v j ,
      Let Rec bs t =[j]=>r v WITH bs ->
      Let Rec bs t =[j]=> v

with eval_bindings_nonrec : Term -> Term -> nat -> Prop :=
  | E_Let_Nil : forall t0 v0 j0,
      t0 =[j0]=> v0 ->
      Let NonRec nil t0 =[ j0 + 1 ]=>nr v0
  | E_Let_TermBind : forall x T t1 j1 v1 j2 v2 bs t0,
      t1 =[j1]=> v1 ->
      ~ is_error v1 ->
      <{ [v1 / x] ({Let NonRec bs t0}) }> =[j2]=>nr v2 ->
      Let NonRec ((TermBind Strict (VarDecl x T) t1) :: bs) t0 =[j1 + 1 + j2]=>nr v2
  | E_Let_TypeBind : forall X K T bs t0 j1 v1,
      <{ [[T / X] ({Let NonRec bs t0}) }> =[j1]=> v1 ->
      Let NonRec ((TypeBind (TyVarDecl X K) T) :: bs) t0 =[j1 + 1]=>nr v1
  (* Error propagation *)
  | E_Error_Let_TermBind : forall x T t1 j1 T' bs t0,
      t1 =[j1]=> Error T' ->
      Let NonRec ((TermBind Strict (VarDecl x T) t1) :: bs) t0 =[j1 + 1]=>nr Error T'

with eval_bindings_rec : list Binding -> Term -> Term -> nat -> Prop :=
  | E_LetRec_Nil : forall bs0 t0 v0 j0,
      t0 =[j0]=> v0 ->
      Let Rec nil t0 =[j0 + 1]=>r v0 WITH bs0
  | E_LetRec_TermBind : forall bs0 s x T bs t0 t1 v1 j1,
      <{ [ {Let Rec bs0 t1} / x] {Let Rec bs t0} }> =[j1]=>r v1 WITH bs0 ->
      Let Rec ((TermBind s (VarDecl x T) t1) :: bs) t0 =[j1 + 1]=>r v1 WITH bs0

where "t '=[' j ']=>' v" := (eval t v j)
and "t '=[' j ']=>nr' v" := (eval_bindings_nonrec t v j)
and "t '=[' j ']=>r' v 'WITH' bs0" := (eval_bindings_rec bs0 t v j).

Scheme eval__ind := Minimality for eval Sort Prop
  with eval_bindings_nonrec__ind := Minimality for eval_bindings_nonrec Sort Prop
  with eval_bindings_rec__ind := Minimality for eval_bindings_rec Sort Prop.

Combined Scheme eval__multind from
  eval__ind,
  eval_bindings_nonrec__ind,
  eval_bindings_rec__ind.

Create HintDb hintdb__eval_no_error.

#[export] Hint Resolve
  E_LamAbs
  E_Apply
  E_TyAbs
  E_TyInst
  E_IWrap
  E_Unwrap
  E_Constant
  E_Builtin
  E_Let
  E_LetRec
  E_Let_Nil
  E_Let_TermBind
  E_Let_TypeBind
  E_LetRec_Nil
  E_LetRec_TermBind
  : hintdb__eval_no_error.

Create HintDb hintdb__eval_with_error.

#[export] Hint Constructors
  eval
  eval_bindings_nonrec
  eval_bindings_rec
  : hintdb__eval_with_error.


Definition terminates t := exists v j, t =[ j ]=> v.
Notation "t '⇓'" := (terminates t) (at level 101).
