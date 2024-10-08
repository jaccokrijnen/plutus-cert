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
  | V_Constr : forall i T vs,
      Forall value vs ->
      value (Constr i T vs)
  (** Unsaturated (partially applied) builtins *)
  | V_Unsaturated : forall nv,
      unsaturated_with 0 nv ->
      value nv

(* Applications of builtins that are unsaturated with n more arguments *)
with unsaturated_with : nat -> term -> Prop :=
  | U_Builtin : forall n f,
      n < arity f ->
      unsaturated_with n (Builtin f)
  | U_Apply : forall n nv v,
      value v ->
      ~ is_error v ->
      unsaturated_with (S n) nv ->
      unsaturated_with n (Apply nv v)
  | U_TyInst : forall n nv T,
      unsaturated_with (S n) nv ->
      unsaturated_with n (TyInst nv T)
  .

#[export] Hint Constructors value : core.
#[export] Hint Constructors unsaturated_with : core.

Scheme value__ind := Minimality for value Sort Prop
  with unsaturated_with__ind := Minimality for unsaturated_with Sort Prop.

Combined Scheme value__multind from
  value__ind,
  unsaturated_with__ind.

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
  (H_Constr : forall (i : nat) (T : ty) (vs : list term), Forall value vs -> Forall P vs -> P (Constr i T vs))
  (H_unsaturated_with : forall nv : term, unsaturated_with 0 nv -> Q 0 nv -> P nv)
  (H_Builtin : forall (n : nat) (f6 : DefaultFun), n < arity f6 -> Q n (Builtin f6))
  (H_Apply : forall (n : nat) (nv v : term), value v -> P v -> ~ is_error v ->
        unsaturated_with (S n) nv -> Q (S n) nv -> Q n (Apply nv v))
  (H_TyInst : forall (n : nat) (nv : term) (T : ty),
        unsaturated_with (S n) nv -> Q (S n) nv -> Q n (TyInst nv T)).
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
  | V_Constr i T ts vs => H_Constr i T ts vs
      ((fix F ts vs := match vs as vs in Forall _ ts return Forall P ts with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ t ts vt vts => @Forall_cons _ _ t ts (value___ind t vt) (F ts vts)
      end) ts vs)
  | V_Unsaturated nv n => H_unsaturated_with nv n (unsaturated_with___ind 0 nv n)
  end
with unsaturated_with___ind (n : nat) (t : term) (n0 : unsaturated_with n t) {struct n0} : Q n t :=
  match n0 in (unsaturated_with n1 t0) return (Q n1 t0) with
  | U_Builtin n1 f9 l => H_Builtin n1 f9 l
  | U_Apply n1 nv v v0 n2 n3 =>
      H_Apply n1 nv v v0 (value___ind v v0) n2 n3 (unsaturated_with___ind (S n1) nv n3)
  | U_TyInst n1 nv T n2 => H_TyInst n1 nv T n2 (unsaturated_with___ind (S n1) nv n2)
  end
.
Combined Scheme value___multind from value___ind, unsaturated_with___ind.
End value_multind.

Definition unsaturated (t : term) := unsaturated_with 0 t.

#[export] Hint Unfold unsaturated : core.

(* Applied builtin that is saturated with n more arguments *)
Inductive saturated_with : nat -> term -> Prop :=
  | S_Builtin : forall n f,
      n = arity f ->
      saturated_with n (Builtin f)
  | S_Apply : forall n nv v,
      value v ->
      ~ is_error v ->
      saturated_with (S n) nv ->
      saturated_with n (Apply nv v)
  | S_TyInst : forall n nv T,
      saturated_with (S n) nv ->
      saturated_with n (TyInst nv T)
  .

#[export] Hint Constructors saturated_with : core.

Definition saturated (t : term) := saturated_with 0 t.

#[export] Hint Unfold saturated : core.

Require Import Lia.

Lemma unsaturated_with__monotone : forall n m nv,
    unsaturated_with n nv ->
    m <= n ->
    unsaturated_with m nv.
Proof with (eauto || (try lia)).
  intros.
  generalize dependent m.
  induction H; intros...
  - destruct f...
    all: econstructor...
  - econstructor...
    eapply IHunsaturated_with...
  - econstructor...
    eapply IHunsaturated_with...
Qed.

Lemma saturated_with__subsumes__unsaturated_with : forall m n nv,
  saturated_with n nv ->
  m < n ->
  unsaturated_with m nv.
Proof with (eauto || (try lia)).
  intros.
  generalize dependent m.
  induction H; intros...
  - subst...
  - econstructor...
    eapply IHsaturated_with...
  - econstructor...
    eapply IHsaturated_with...
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

Definition dec_unsaturated_with (n : nat) (t : term) :=
  match t with
    | Builtin f   => dec_value' n t
    | Apply nv v  => dec_value' n t
    | TyInst nv T => dec_value' n t
    | _           => false
  end.

Lemma dec_value_value : forall t, dec_value t = true -> value t.
Admitted.

Lemma dec_unsaturated_with_unsaturated_with : forall n t, dec_unsaturated_with n t = true -> unsaturated_with n t.
Admitted.
