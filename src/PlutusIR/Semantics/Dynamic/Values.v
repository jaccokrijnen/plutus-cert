Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
From Coq Require Import
  Lists.List
  Bool.Bool
  Arith.PeanoNat.
Import PeanoNat.Nat.

Inductive is_error : term -> Prop :=
  | IsError : forall T,
      is_error (Error T).

Inductive value : term -> Prop :=
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
  | V_Constr : forall i vs,
      Forall value vs ->
      value (Constr i vs)
  (** Builtins *)
  | V_Neutral : forall nv,
      neutral_value 0 nv ->
      value nv
  (** If-Then-Else constructs

      NOTE (2021-11-4): Removed separate treatment of if-then-else for the sake of simplicity.
  *)
  (* | V_If :
      value (Builtin IfThenElse)
  | V_If1 : forall T,
      value (TyInst (Builtin IfThenElse) T)
  | V_If2 : forall T cond,
      value (Apply (TyInst (Builtin IfThenElse) T) cond)
  | V_If3 : forall T cond t,
      value (Apply (Apply (TyInst (Builtin IfThenElse) T) cond) t) *)

with neutral_value : nat -> term -> Prop :=
  | NV_Builtin : forall n f,
      (* NOTE (2021-11-4): Removed separate treatment of if-then-else for the sake of simplicity. *)
      (* f <> IfThenElse -> *)
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

Section value_multind.
Context
  (P : term -> Prop)
  (Q : nat -> term -> Prop).
Context
  (H_LamAbs : forall (x : String.string) (T : ty) (t0 : term), P (LamAbs x T t0))
  (H_TyAbs : forall (X : String.string) (K : kind) (t : term), P (TyAbs X K t))
  (H_IWrap : forall (F T : ty) (v : term), value v -> P v -> ~ is_error v -> P (IWrap F T v))
  (H_Constant : forall c : constant, P (Constant c))
  (H_Error : forall T : ty, P (Error T))
  (H_Constr : forall (i : nat) (vs : list term), Forall value vs -> Forall P vs -> P (Constr i vs))
  (H_Neutral : forall nv : term, neutral_value 0 nv -> Q 0 nv -> P nv)
  (H_Builtin : forall (n : nat) (f6 : DefaultFun), n < arity f6 -> Q n (Builtin f6))
  (H_Apply : forall (n : nat) (nv v : term), value v -> P v -> ~ is_error v ->
        neutral_value (S n) nv -> Q (S n) nv -> Q n (Apply nv v))
  (H_TyInst : forall (n : nat) (nv : term) (T : ty),
        neutral_value (S n) nv -> Q (S n) nv -> Q n (TyInst nv T)).
Fixpoint values__ind (H_value : forall (t : term), value t -> P t) (ts : list term) (vs : Forall value ts): Forall P ts :=
  match vs as vs in Forall _ ts return Forall P ts with
    | Forall_nil _ => Forall_nil _
    | @Forall_cons _ _ x xs vx vxs => @Forall_cons _ _ x xs (H_value x vx) (values__ind H_value xs vxs)
  end.
Fixpoint value___ind (t : term) (v : value t) {struct v} : P t :=
  match v in (value t0) return (P t0) with
  | V_LamAbs x T t0 => H_LamAbs x T t0
  | V_TyAbs X K t0 => H_TyAbs X K t0
  | V_IWrap F1 T v0 v1 n => H_IWrap F1 T v0 v1 (value___ind v0 v1) n
  | V_Constant u => H_Constant u
  | V_Error T => H_Error T
  | V_Constr i ts vs => H_Constr i ts vs
      ((fix F ts vs := match vs as vs in Forall _ ts return Forall P ts with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ t ts vt vts => @Forall_cons _ _ t ts (value___ind t vt) (F ts vts)
      end) ts vs)
  | V_Neutral nv n => H_Neutral nv n (neutral___ind 0 nv n)
  end
with neutral___ind (n : nat) (t : term) (n0 : neutral_value n t) {struct n0} : Q n t :=
  match n0 in (neutral_value n1 t0) return (Q n1 t0) with
  | NV_Builtin n1 f9 l => H_Builtin n1 f9 l
  | NV_Apply n1 nv v v0 n2 n3 =>
      H_Apply n1 nv v v0 (value___ind v v0) n2 n3 (neutral___ind (S n1) nv n3)
  | NV_TyInst n1 nv T n2 => H_TyInst n1 nv T n2 (neutral___ind (S n1) nv n2)
  end
.
Combined Scheme value___multind from value___ind, neutral___ind.
End value_multind.

Definition neutral (t : term) := neutral_value 0 t.

#[export] Hint Unfold neutral : core.

Inductive fully_applied_neutral : nat -> term -> Prop :=
  | FA_Builtin : forall n f,
      (* NOTE (2021-11-4): Removed separate treatment of if-then-else for the sake of simplicity. *)
      (* f <> IfThenElse -> *)
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

Definition fully_applied (t : term) := fully_applied_neutral 0 t.

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


Definition is_error_b (t : term) :=
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
  dec_value' (n : nat) (t : term) {struct t} :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => dec_value' n v && negb (is_error_b v)
    | Constant u    => true
    | Error T       => true


    (* Duplication for the termination checker *)
    | Builtin f   => ltb n (arity f)
    | Apply nv v  => dec_value' n v && negb (is_error_b v) && dec_value' (S n) nv
    | TyInst nv T => dec_value' (S n) nv
    | _ => false
  end
  .

Definition dec_value := dec_value' 0.

Definition dec_neutral_value (n : nat) (t : term) :=
  match t with
    | Builtin f   => dec_value' n t
    | Apply nv v  => dec_value' n t
    | TyInst nv T => dec_value' n t
    | _           => false
  end.

Lemma dec_value_value : forall t, dec_value t = true -> value t.
Admitted.

Lemma dec_neutral_value_neutral_value : forall n t, dec_neutral_value n t = true -> neutral_value n t.
Admitted.
