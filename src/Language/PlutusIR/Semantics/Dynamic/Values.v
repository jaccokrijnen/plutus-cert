Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.


(** * Values *)

Inductive value : Term -> Prop :=
  | V_TyAbs : forall bX K t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (TyAbs bX K t0)
  | V_LamAbs : forall bx T t0,
      value (LamAbs bx T t0)
  | V_Constant : forall u,
      value (Constant u)
  | V_Builtin : forall v,
      value_builtin v ->
      value v
  | V_Error : forall T,
      value (Error T)
  | V_IWrap : forall F T t0,
      (* TODO: Should the line below be included? *)
      value t0 ->
      value (IWrap F T t0)

with value_builtin : Term -> Prop :=
| V_Builtin0 : forall f,
    0 < arity f ->
    value_builtin (Builtin f)
| V_Builtin1 : forall f v1,
    1 < arity f ->
    value v1 ->
    value_builtin (Apply (Builtin f) v1)
| V_Builtin2 : forall f v1 v2,
    2 < arity f ->
    value v1 ->
    value v2 ->
    value_builtin (Apply (Apply (Builtin f) v1) v2)
| V_Builtin1_WithTyInst : forall f T,
    1 < arity f ->
    value_builtin (TyInst (Builtin f) T)
| V_Builtin2_WithTyInst : forall f T v1,
    2 < arity f ->
    value v1 ->
    value_builtin (Apply (TyInst (Builtin f) T) v1)
| V_Builtin3_WithTyInst : forall f T v1 v2,
    3 < arity f ->
    value v1 ->
    value v2 ->
    value_builtin (Apply (Apply (TyInst (Builtin f) T) v1) v2).