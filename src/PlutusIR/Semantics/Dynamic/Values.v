Require Import PlutusCert.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
From Coq Require Import Bool.Bool Arith.PeanoNat.
Import PeanoNat.Nat.

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
.

#[export] Hint Constructors value : core.

Scheme value__ind := Minimality for value Sort Prop.

Require Import Lia.

Definition is_error_b (t : Term) :=
  match t with
    | Error T => true
    | _       => false
  end.

Lemma is_error_is_error_b : forall t, is_error_b t = true -> is_error t.
Proof.
  intros t H.
  destruct t; inversion H.
  constructor.
Qed.

Fixpoint
  dec_value (t : Term) {struct t} :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => dec_value v && negb (is_error_b v)
    | Constant u    => true
    | Error T       => true
    | _ => false
  end
  .

Lemma dec_value_value : forall t, dec_value t = true -> value t.
Admitted.
