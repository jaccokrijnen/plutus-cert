From PlutusCert Require Import STLC_named.

(** Normal types *)
Inductive normal_Ty : term -> Prop :=
  | NO_TyLam : forall bX K T,
      normal_Ty T ->
      normal_Ty (tmlam bX K T)
  | NO_neutral : forall T,
      neutral_Ty T ->
      normal_Ty T

with neutral_Ty : term -> Prop :=
  | NE_TyVar : forall X,
      neutral_Ty (tmvar X)
  | NE_TyApp : forall T1 T2,
      neutral_Ty T1 ->
      normal_Ty T2 ->
      neutral_Ty (tmapp T1 T2).

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : term -> term -> Prop :=
  | N_BetaReduce : forall bX K T1 T2 T1n T2n T,
      normalise T1 (tmlam bX K T1n) ->
      normalise T2 T2n ->
      normalise (substituteTCA bX T2n T1n) T ->
      normalise (tmapp T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n ->
      normalise T2 T2n ->
      normalise (tmapp T1 T2) (tmapp T1n T2n)
  | N_TyLam : forall bX K T0 T0n,
      normalise T0 T0n ->
      normalise (tmlam bX K T0) (tmlam bX K T0n)
  | N_TyVar : forall X,
      normalise (tmvar X) (tmvar X)
  .

#[export] Hint Constructors normalise : core.


