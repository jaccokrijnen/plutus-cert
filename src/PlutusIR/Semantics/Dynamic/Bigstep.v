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
  | E_NeutralBuiltin : forall f,
      (* NOTE (2021-11-4): Removed separate treatment of if-then-else for the sake of simplicity. *)
      (* f <> IfThenElse -> *)
      Builtin f =[0]=> Builtin f
  | E_NeutralApply : forall nv v,
      neutral (Apply nv v) ->
      (Apply nv v) =[0]=> (Apply nv v)
  | E_NeutralTyInst : forall nv T,
      neutral (TyInst nv T) ->
      (TyInst nv T) =[0]=> (TyInst nv T)
  | E_NeutralApplyPartial: forall t1 t2 nv1 v2 v0 j1 j2 j0,
      ~ neutral (Apply t1 t2) ->
      t1 =[j1]=> nv1 ->
      neutral nv1 ->
      t2 =[j2]=> v2 ->
      ~ is_error v2 ->
      Apply nv1 v2 =[j0]=> v0 ->
      Apply t1 t2 =[j1 + j2 + 1 + j0]=> v0
  | E_NeutralTyInstPartial : forall t1 T nv1 v0 j1 j0,
      ~ neutral (TyInst t1 T) ->
      t1 =[j1]=> nv1 ->
      neutral nv1 ->
      TyInst nv1 T =[j0]=> v0 ->
      TyInst t1 T =[j1 + 1 + j0]=> v0
  | E_NeutralApplyFull: forall nv1 v2 v,
      fully_applied (Apply nv1 v2) ->
      compute_defaultfun (Apply nv1 v2) = Datatypes.Some v ->
      Apply nv1 v2 =[1]=> v
  | E_NeutralTyInstFull: forall nv1 v T,
      fully_applied (TyInst nv1 T) ->
      compute_defaultfun (TyInst nv1 T) = Datatypes.Some v ->
      TyInst nv1 T =[1]=> v
  (** Builtins: If-Then-Else

      We handle this built-in function separately because it has a unique behaviour:
      The ``then''-branch should only be evaluated when the condition is true,
      and the opposite is true for the ``else''-branch.

      NOTE (2021-11-4): Removed separate treatment of if-then-else for the sake of simplicity.
  *)
  (* | E_IfBuiltin :
      Builtin IfThenElse =[0]=> Builtin IfThenElse
  | E_IfTyInst : forall t1 T j1,
      t1 =[j1]=> Builtin IfThenElse ->
      TyInst t1 T =[j1]=> TyInst (Builtin IfThenElse) T
  | E_IfCondition : forall t1 t2 T j1,
      t1 =[j1]=> TyInst (Builtin IfThenElse) T ->
      Apply t1 t2 =[j1]=> Apply (TyInst (Builtin IfThenElse) T) t2
  | E_IfThenBranch : forall t1 j1 T t2 t3,
      t1 =[j1]=> Apply (TyInst (Builtin IfThenElse) T) t2 ->
      Apply t1 t3 =[j1]=> Apply (Apply (TyInst (Builtin IfThenElse) T) t2) t3
  | E_IfElseBranch : forall t1 j1 T t2 t3 t4 j0 v0,
      t1 =[j1]=> Apply (Apply (TyInst (Builtin IfThenElse) T) t2) t3 ->
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) t2) t3) t4 =[j0]=> v0 ->
      Apply t1 t4 =[j1 + j0]=> v0
  | E_IfTrue : forall T t1 t2 t3 j1 j2 v2,
      t1 =[j1]=> Constant (Some (ValueOf DefaultUniBool true)) ->
      t2 =[j2]=> v2 ->
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) t1) t2) t3 =[j1 + 1 + j2]=> v2
  | E_IfFalse : forall T t1 t2 t3 j1 j3 v3,
      t1 =[j1]=> Constant (Some (ValueOf DefaultUniBool false)) ->
      t3 =[j3]=> v3 ->
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) t1) t2) t3 =[j1 + 1 + j3]=> v3 *)
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
  E_NeutralBuiltin
  E_NeutralApply
  E_NeutralTyInst
  E_NeutralApplyPartial
  E_NeutralTyInstPartial
  E_NeutralApplyFull
  E_NeutralTyInstFull
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
