From PlutusCert Require Import STLC_DB.

(** Normal types *)
Inductive normal_Ty : term -> Prop :=
  | NO_TyLam : forall K T,
      normal_Ty T ->
      normal_Ty (tmlam K T)
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
      
Fixpoint is_normal (t : term) : bool :=
  match t with
  | tmlam K T => is_normal T
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  end

with is_neutral (t : term) : bool :=
  match t with
  | tmvar X => true
  | tmapp T1 T2 => is_neutral T1 && is_normal T2
  | _ => false
  end.

Scheme normal_Ty__ind := Minimality for normal_Ty Sort Prop
  with neutral_Ty__ind := Minimality for neutral_Ty Sort Prop.

Combined Scheme normal_Ty__multind from
  normal_Ty__ind,
  neutral_Ty__ind.

#[export] Hint Constructors normal_Ty neutral_Ty : core.

(** Type normalisation *)
Inductive normalise : term -> term -> Prop :=
  | N_BetaReduce : forall K T1 T2 T1n T2n T,
      normalise T1 (tmlam K T1n) ->
      normalise T2 T2n ->
      normalise T1n.[T2n/] T ->
      normalise (tmapp T1 T2) T
  | N_TyApp : forall T1 T2 T1n T2n,
      normalise T1 T1n ->
      neutral_Ty T1n ->
      normalise T2 T2n ->
      normalise (tmapp T1 T2) (tmapp T1n T2n)
  | N_TyLam : forall K T0 T0n,
      normalise T0 T0n ->
      normalise (tmlam K T0) (tmlam K T0n)
  | N_TyVar : forall i,
      normalise (tmvar i) (tmvar i)
  .

#[export] Hint Constructors normalise : core.

Lemma normalise_ex1 :
  normalise (tmvar 0) (tmvar 0).
Proof.
  apply N_TyVar.
Qed.

Lemma normalise_ex2 :
  normalise (tmapp (tmlam tp_base (tmvar 0)) (tmvar 0)) (tmvar 0).
Proof.
  apply N_BetaReduce with (K := tp_base) (T1n := tmvar 0) (T2n := tmvar 0).
  - apply N_TyLam.
    apply N_TyVar.
  - apply N_TyVar.
  - simpl. (* the substitution seems to be defined correctly for var at least.*)
    apply N_TyVar.
Qed.

(* (\. 0 1) 0 => 0 0
  Is that well typed? *)
Lemma normalise_ex3 :
  normalise (tmapp 
              (tmlam tp_base (tmapp (tmvar 0) (tmvar 1))) 
              (tmvar 0)) 
    (tmapp (tmvar 0) (tmvar 0)).
Proof.
  apply N_BetaReduce with 
    (K := tp_base) 
    (T1n := (tmapp (tmvar 0) (tmvar 1))) 
    (T2n := (tmvar 0)).
  all: repeat constructor.
Qed.
   
  




