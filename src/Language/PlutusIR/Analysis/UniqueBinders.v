Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Util.

Import Coq.Lists.List.
Import Coq.Strings.String.
Local Open Scope string_scope.

From QuickChick Require Import QuickChick.

Inductive unique_ty : Ty -> Prop :=
  | UNI_TyFun : forall T1 T2,
      unique_ty T1 ->
      unique_ty T2 ->
      unique_ty (Ty_Fun T1 T2)
  | UNI_TyBuiltin : forall st,
      unique_ty (Ty_Builtin st)
  | UNI_TyVar : forall X,
      unique_ty (Ty_Var X)
  | UNI_TyForall : forall X K T,
      ~ appears_bound_in_ty X T ->
      unique_ty T ->
      unique_ty (Ty_Forall X K T)
  | UNI_TyIFix : forall F T,
      unique_ty F ->
      unique_ty T ->
      unique_ty (Ty_IFix F T)
  | UNI_TyLam : forall X K T,
      ~ appears_bound_in_ty X T ->
      unique_ty T ->
      unique_ty (Ty_Lam X K T)
  | UNI_TyApp : forall T1 T2,
      unique_ty T1 ->
      unique_ty T2 ->
      unique_ty (Ty_App T1 T2)
  .

QCDerive DecOpt for (unique_ty ty).

Instance unique_ty_DecOpt_sound ty : DecOptSoundPos (unique_ty ty).
Proof. derive_sound. Qed.

(* FIXME: I don't think you can derive soundness for relations with negative constraints, unless you
    proof a negative completeness proof for said constrain *)
Instance unique_ty_DecOpt_complete ty : DecOptCompletePos (unique_ty ty).
Proof. idtac "Admitted: unique_ty_decopt_complete". Admitted.

Instance unique_ty_DecOpt_monotonic ty : DecOptSizeMonotonic (unique_ty ty).
Proof. derive_mon. Qed.

Inductive unique_tm : Term -> Prop :=
  | UNI_Var : forall x,
      unique_tm (Var x)
  | UNI_LamAbs : forall x T t,
      ~ appears_bound_in_tm x t ->
      unique_tm t ->
      unique_ty T ->
      unique_tm (LamAbs x T t)
  | UNI_App : forall t1 t2,
      unique_tm t1 ->
      unique_tm t2 ->
      unique_tm (Apply t1 t2)
  | UNI_TyAbs : forall X K t,
      ~ appears_bound_in_ann X t ->
      unique_tm t ->   
      unique_tm (TyAbs X K t)
  | UNI_TyInst : forall t T,
      unique_tm t ->
      unique_ty T ->
      unique_tm (TyInst t T)
  | UNI_IWrap : forall F T t,
      unique_ty F ->
      unique_ty T ->
      unique_tm t ->
      unique_tm (IWrap F T t)
  | UNI_Unwrap : forall t,
      unique_tm t ->
      unique_tm (Unwrap t)
  | UNI_Constant : forall sv,
      unique_tm (Constant sv)
  | UNI_Builtin : forall f,
      unique_tm (Builtin f)
  | UNI_Error : forall T,
      unique_ty T ->
      unique_tm (Error T)
  | UNI_Let_Nil : forall recty t0,
      unique_tm t0 ->
      unique_tm (Let recty nil t0)
  | UNI_Let_TermBind : forall recty stricty x T t bs t0,
      ~ appears_bound_in_tm x t ->
      ~ appears_bound_in_tm x (Let recty bs t0) ->
      unique_tm t ->
      unique_tm (Let recty bs t0) ->
      unique_tm (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
  | UNI_Let_TypeBind : forall recty X K T bs t0,
      ~ appears_bound_in_ty X T ->
      ~ appears_bound_in_ann X (Let recty bs t0) ->
      unique_ty T ->
      unique_tm (Let recty bs t0) ->
      unique_tm (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
  | UNI_Let_DatatypeBind : forall recty X K YKs mfunc cs t0 bs,
      ~ appears_bound_in_ann X (Let recty bs t0) ->
      unique_tm (Let recty bs t0) ->
      unique_tm (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0).

QCDerive DecOpt for (unique_tm tm).

Instance unique_tm_DecOpt_sound tm : DecOptSoundPos (unique_tm tm).
Proof. derive_sound. Qed.

(* FIXME: I don't think you can derive soundness for relations with negative constraints, unless you
    proof a negative completeness proof for said constrain *)
Instance unique_tm_DecOpt_complete tm : DecOptCompletePos (unique_tm tm).
Proof. idtac "Admitted: unique_tm_DecOpt_complete". Admitted.

Instance unique_tm_DecOpt_monotonic ty : DecOptSizeMonotonic (unique_ty ty).
Proof. derive_mon. Qed.
