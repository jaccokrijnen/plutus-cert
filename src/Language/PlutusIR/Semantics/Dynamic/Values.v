Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.


(** * Values *)

Inductive value : Term -> Prop :=
  | V_TyAbs : forall bX K t0,
      value (TyAbs bX K t0)
  | V_LamAbs : forall bx T t0,
      value (LamAbs bx T t0)
  | V_Constant : forall u,
      value (Constant u)
  | V_Error : forall T,
      value (Error T)
  | V_IWrap : forall F T t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (IWrap F T t0)
  (** If-Then-Else constructs *)
  | V_If :
      value (Builtin IfThenElse)
  | V_IfTyInst : forall T,
      value (TyInst (Builtin IfThenElse) T)
  | V_IfCondition : forall T cond,
      value (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))))
  | V_IfThenBranch : forall T cond t_then,
      value (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))) t_then)

  (* Extras *)
  | V_ExtBuiltin : forall f args,
      length args < arity f ->
      value (ExtBuiltin f args).

#[export] Hint Constructors value : core.