From PlutusCert Require Import PlutusIRSOP TypeSubstitutionSOP plutus_util.
Require Import Strings.String.


(** Normal types *)
Inductive normal_Ty : ty -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Lam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T
  | NO_TyFun : forall T1 T2,
      normal_Ty T1 ->
      normal_Ty T2 ->
      normal_Ty (Ty_Fun T1 T2)
  | NO_TyForall : forall bX K T,
      normal_Ty T ->
      normal_Ty (Ty_Forall bX K T)
  | NO_TyIFix : forall F T,
      normal_Ty F ->
      normal_Ty T ->
      normal_Ty (Ty_IFix F T)
  | NO_TyBuiltin : forall st,
      normal_Ty (Ty_Builtin st)
  | NO_TySOP : forall (Tss : (list ty)),
      ForallSet (fun T => normal_Ty T) Tss ->
      normal_Ty (Ty_SOP Tss)

with neutral_Ty : ty -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (Ty_Var X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (Ty_App T1 T2).

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : ty -> ty -> Set :=
  | N_BetaReduce : forall bX K T1 T2 T1n T2n T,
      normalise T1 (Ty_Lam bX K T1n) ->     (* TyApp (Lam bX Kind_Base (Ty_Var bX)) (Lam bY Kind_Base (Ty_Var bY)) -> Lam bY Kind_Base (Ty_Var bY) *)
      normalise T2 T2n ->
      normalise (substituteTCA bX T2n T1n) T ->
      normalise (Ty_App T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n ->
      normalise T2 T2n ->
      normalise (Ty_App T1 T2) (Ty_App T1n T2n)
  | N_TyFun : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      normalise T2 T2n ->
      normalise (Ty_Fun T1 T2) (Ty_Fun T1n T2n)
  | N_TyForall : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Forall bX K T0) (Ty_Forall bX K T0n)
  | N_TyLam : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (Ty_Lam bX K T0) (Ty_Lam bX K T0n)
  | N_TyVar : forall X,
      normalise (Ty_Var X) (Ty_Var X)
  | N_TyIFix : forall F T Fn Tn,
      normalise F Fn ->
      normalise T Tn ->
      normalise (Ty_IFix F T) (Ty_IFix Fn Tn)
  | N_TyBuiltin : forall (st : DefaultUni),
      normalise (Ty_Builtin st) (Ty_Builtin st)
  | N_TySOP : forall (Tss Tss' : (list ty)),
      ForallSetPair normalise Tss Tss' ->
      normalise (Ty_SOP Tss) (Ty_SOP Tss')
  .

#[export] Hint Constructors normalise : core.