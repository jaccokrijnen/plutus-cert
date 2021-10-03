Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.



(** * Big-step operational semantics *)

(** ** Implementation of big-step semantics as an inductive datatype *)
Reserved Notation "t '=[' j ']=>' v"(at level 40).
Inductive eval : Term -> Term -> nat -> Prop :=
  (** Let-bindings *)
  | E_Let : forall bs t v j,
      eval_bindings_nonrec (Let NonRec bs t) v j ->
      (Let NonRec bs t) =[j]=> v
  | E_LetRec : forall bs t v j ,
      eval_bindings_rec bs (Let Rec bs t) v j ->
      (Let Rec bs t) =[j]=> v
  (** Others *)
  | E_TyAbs : forall X K t,
      TyAbs X K t =[0]=> TyAbs X K t
  | E_LamAbs : forall x T t,
      LamAbs x T t =[0]=> LamAbs x T t
  | E_Apply : forall t1 t2 x T t0 v2 v0 j1 j2 j0,
      t1 =[j1]=> LamAbs x T t0 ->
      t2 =[j2]=> v2 ->
      <{ [v2 / x] t0 }> =[j0]=> v0 ->
      Apply t1 t2 =[j1 + j2 + 1 + j0]=> v0
  | E_Constant : forall a,
      Constant a =[0]=> Constant a
  (* Builtins *)
  | E_Builtin : forall f,
      Builtin f =[0]=> Builtin f
  | E_ApplyBuiltin1 : forall t1 t2 v1 v2 j1 j2,
      t1 =[j1]=> v1 ->
      value_builtin v1 ->
      t2 =[j2]=> v2 ->
      value_builtin (Apply v1 v2) ->
      Apply t1 t2 =[j1 + j2]=> Apply v1 v2
  | E_ApplyBuiltin2 : forall t1 t2 v1 v2 v0 j1 j2,
      t1 =[j1]=> v1 ->
      value_builtin v1 ->
      t2 =[j2]=> v2 ->
      ~(value_builtin (Apply v1 v2)) ->
      compute_defaultfun (Apply v1 v2) = Datatypes.Some v0 ->
      Apply t1 t2 =[j1 + j2 + 1]=> v0
  (** Builtins: If-Then-Else 

      We handle this built-in function separately because it has a unique behaviour:
      The ``then''-branch should only be evaluated when the condition is true,
      and the opposite is true for the ``else''-branch.
  *)
  | E_IfTyInst : forall t1 T j1,
      t1 =[j1]=> Builtin IfThenElse ->
      TyInst t1 T =[j1]=> TyInst (Builtin IfThenElse) T
  | E_IfCondition : forall t_b t_c T cond j_b j_c,
      t_b =[j_b]=> TyInst (Builtin IfThenElse) T ->
      t_c =[j_c]=> Constant (Some (ValueOf DefaultUniBool cond)) ->
      Apply t_b t_c =[j_b + j_c]=> Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))
  | E_IfThenBranch : forall t_bc t_t T cond j_bc,
      t_bc =[j_bc]=> Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) ->
      Apply t_bc t_t =[j_bc]=> Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))) t_t
  | E_IfTrue : forall t_bct t_t T v_t t_e j_bct j_t,
      t_bct =[j_bct]=> Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t ->
      t_t =[j_t]=> v_t ->
      Apply t_bct t_e =[j_bct + j_t]=> v_t
  | E_IfFalse : forall t_bct t_t T v_e t_e j_bct j_e,
      t_bct =[j_bct]=> Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t ->
      t_e =[j_e]=> v_e ->
      Apply t_bct t_e =[j_bct + j_e]=> v_e
  (* Type instantiation *)
  | E_TyInst : forall t1 T2 X K t0 v0 j1 j0,
      t1 =[j1]=> TyAbs X K t0 ->
      <{ [[T2 / X] t0 }> =[j0]=> v0 ->
      TyInst t1 T2 =[j1 + 1 + j0]=> v0
  (* Errors and their propagation *)
  | E_Error : forall T,
      Error T =[0]=> Error T
  (* Wrap and unwrap *)
  | E_IWrap : forall F T t0 v0 j0,
      t0 =[j0]=> v0 ->
      IWrap F T t0 =[j0]=> IWrap F T v0
  | E_Unwrap : forall t0 F T v0 j0,
      t0 =[j0]=> IWrap F T v0 ->
      Unwrap t0 =[j0 + 1]=> v0
  (* TODO: Should there be a rule for type reduction? *)

  (* TODO: Errors propagate *)

with eval_bindings_nonrec : Term -> Term -> nat -> Prop :=
  | E_NilB_NonRec : forall t v j,
      t =[j]=> v ->
      eval_bindings_nonrec (Let NonRec nil t) v (S j)
  | E_ConsB_NonRec : forall s x T tb bs t vb v jb j,
      tb =[jb]=> vb ->
      eval_bindings_nonrec <{ [vb / x] ({Let NonRec bs t}) }> v j ->
      eval_bindings_nonrec (Let NonRec ((TermBind s (VarDecl x T) tb) :: bs) t) v (jb + 1 + j)

with eval_bindings_rec : list Binding -> Term -> Term -> nat -> Prop :=
  | E_NilB_Rec : forall bs0 t v j,
      t =[j]=> v ->
      eval_bindings_rec bs0 (Let Rec nil t) v (S j)
  | E_ConsB_Rec : forall bs0 s x T tb bs t v j,
      eval_bindings_rec bs0 <{ [ {Let Rec bs0 tb} / x] {Let Rec bs t} }>  v j ->
      eval_bindings_rec bs0 (Let Rec ((TermBind s (VarDecl x T) tb) :: bs) t) v (j + 1)

where "t '=[' j ']=>' v" := (eval t v j).

Scheme eval__ind := Minimality for eval Sort Prop
  with eval_bindings_nonrec__ind := Minimality for eval_bindings_nonrec Sort Prop
  with eval_bindings_rec__ind := Minimality for eval_bindings_rec Sort Prop.

Combined Scheme eval__multind from 
  eval__ind,
  eval_bindings_nonrec__ind,
  eval_bindings_rec__ind.