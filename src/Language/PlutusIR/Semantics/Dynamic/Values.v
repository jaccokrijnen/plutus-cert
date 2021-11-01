Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.

Inductive is_error : Term -> Prop :=
  | IsError : forall T,
      is_error (Error T).

Inductive value : Term -> Prop :=
  | V_LamAbs : forall x T t0,
      value (LamAbs x T t0) 
  | V_TyAbs : forall X K t,
      value (TyAbs X K t)
  | V_IWrap : forall F T v,
      value v ->
      ~ is_error v ->
      value (IWrap F T v)
  | V_Constant : forall u,
      value (Constant u)
  | V_Error : forall T,
      value (Error T)
  (** Builtins *) 
  | V_Neutral : forall nv,
      neutral_value 0 nv ->
      value nv
  (** If-Then-Else constructs *)
  | V_If : 
      value (Builtin IfThenElse)
  | V_If1 : forall T,
      value (TyInst (Builtin IfThenElse) T)
  | V_If2 : forall T cond,
      value (Apply (TyInst (Builtin IfThenElse) T) cond)
  | V_If3 : forall T cond t,
      value (Apply (Apply (TyInst (Builtin IfThenElse) T) cond) t)

with neutral_value : nat -> Term -> Prop :=
  | NV_Builtin : forall n f,
      f <> IfThenElse ->
      n < arity f ->
      neutral_value n (Builtin f)
  | NV_Apply : forall n nv v,
      value v ->
      ~ is_error v ->
      neutral_value (S n) nv ->
      neutral_value n (Apply nv v)
  | NV_TyInst : forall n nv T,
      neutral_value (S n) nv ->
      neutral_value n (TyInst nv T)
  .

#[export] Hint Constructors value : core.
#[export] Hint Constructors neutral_value : core.

Scheme value__ind := Minimality for value Sort Prop
  with neutral_value__ind := Minimality for neutral_value Sort Prop.

Combined Scheme value__multind from 
  value__ind,
  neutral_value__ind.

Definition neutral (t : Term) := neutral_value 0 t.

#[export] Hint Unfold neutral : core.

Inductive fully_applied_neutral : nat -> Term -> Prop :=
  | FA_Builtin : forall n f,
      f <> IfThenElse ->
      n = arity f ->
      fully_applied_neutral n (Builtin f)
  | FA_Apply : forall n nv v,
      value v ->
      ~ is_error v ->
      fully_applied_neutral (S n) nv ->
      fully_applied_neutral n (Apply nv v)
  | FA_TyInst : forall n nv T,
      fully_applied_neutral (S n) nv ->
      fully_applied_neutral n (TyInst nv T)
  .

#[export] Hint Constructors fully_applied_neutral : core.

Definition fully_applied (t : Term) := fully_applied_neutral 0 t.

#[export] Hint Unfold fully_applied : core.

Require Import Lia.

Lemma neutral_value__monotone : forall n m nv,
    neutral_value n nv ->
    m <= n ->
    neutral_value m nv.
Proof with (eauto || (try lia)).
  intros.
  generalize dependent m.
  induction H; intros...
  - destruct f...
    all: econstructor...
  - econstructor...
    eapply IHneutral_value...
  - econstructor...
    eapply IHneutral_value...
Qed.

Lemma fully_applied_neutral__subsumes__neutral_value : forall m n nv,
  fully_applied_neutral n nv ->
  m < n ->
  neutral_value m nv.
Proof with (eauto || (try lia)).
  intros.
  generalize dependent m.
  induction H; intros...
  - subst...
  - econstructor...
    eapply IHfully_applied_neutral...
  - econstructor...
    eapply IHfully_applied_neutral...
Qed.