Require Import PlutusCert.Language.PlutusIR.
Require Import PlutusCert.Util.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
From Coq Require Import Bool.Bool Arith.PeanoNat.

From QuickChick Require Import QuickChick.


Inductive is_error : Term -> Prop :=
  | IsError : forall T,
      is_error (Error T).

QCDerive DecOpt for (is_error tm).

Instance is_error_DecOpt_sound tm : DecOptSoundPos (is_error tm).
Proof. derive_sound. Qed.

Instance is_error_ty_DecOpt_complete tm : DecOptCompletePos (is_error tm).
Proof. derive_complete. Qed.

Instance is_error_ty_DecOpt_monotonic tm : DecOptSizeMonotonic (is_error tm).
Proof. derive_mon. Qed.




Inductive neutral_flag :=
  | NFT
  | NFF.

Inductive value' : neutral_flag -> nat -> Term -> Prop :=
  | V_LamAbs : forall n x T t0,
      value' NFF n (LamAbs x T t0) 
  | V_TyAbs : forall n X K t,
      value' NFF n (TyAbs X K t)
  | V_IWrap : forall n F T v,
      value' NFF n v ->
      ~ is_error v ->
      value' NFF n (IWrap F T v)
  | V_Constant : forall n u,
      value' NFF n (Constant u)
  | V_Error : forall n T,
      value' NFF n (Error T)
  (** Builtins *) 
  | V_Neutral_Builtin : forall nf n f,
      (* lt_nat (S n) (arity f) -> *)
      value' nf n (Builtin f)
  | V_Neutral_Apply : forall nf n nv v,
      value' NFF 0 v ->
      ~ is_error v ->
      value' NFT (S n) nv ->
      value' nf n (Apply nv v)
  | V_Neutral_TyInst : forall nf n nv T,
      value' NFT (S n) nv ->
      value' nf n (TyInst nv T).

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

#[export] Hint Constructors value' : core.

Scheme value__ind := Minimality for value' Sort Prop.

Combined Scheme value__multind from 
  value__ind.

Definition value (tm : Term) := value' NFF 0 tm.
Definition neutral_value (n : nat) (t : Term) := value' NFT n t.
Definition neutral (t : Term) := neutral_value 0 t.

#[export] Hint Unfold neutral : core.
#[export] Hint Unfold value : core.


QCDerive DecOpt for (value' nt n tm).

Instance value'_DecOpt_sound nt n tm : DecOptSoundPos (value' nt n tm).
Proof. derive_sound. Qed.

(* Some extra work is necessary to get around the value alias, QuickChick cannot do this itself *)
Instance DecOptvalue tm : DecOpt (value tm) :=
  {| decOpt s := @decOpt (value' NFF 0 tm) _ s |}.

Instance value_DecOpt_sound tm : DecOptSoundPos (value tm).
Proof. unfold value. unfold DecOptSoundPos. intros. apply sound with (s0 := s). apply H. Qed.




Inductive fully_applied_neutral : nat -> Term -> Prop :=
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

Definition fully_applied (t : Term) := fully_applied_neutral 0 t.

#[export] Hint Unfold fully_applied : core.

Require Import Lia.

Lemma neutral_value__monotone : forall n m nv,
    neutral_value n nv ->
    m <= n ->
    neutral_value m nv.
Proof with (eauto || (try lia)).
  unfold neutral_value.
  intros.
  generalize dependent m.
  induction H; intros...
  - constructor; try assumption.
    apply IHvalue'2.
    apply le_n_S.
    apply H2.
  - econstructor...
    eapply IHvalue'...
Qed.

Lemma fully_applied_neutral__subsumes__neutral_value : forall m n nv,
  fully_applied_neutral n nv ->
  m < n ->
  neutral_value m nv.
Proof with (eauto || (try lia)).
  unfold neutral_value.
  intros.
  generalize dependent m.
  induction H; intros...
  - econstructor...
    eapply IHfully_applied_neutral...
  - econstructor...
    eapply IHfully_applied_neutral...
Qed.


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
  is_value' (n : nat) (t : Term) {struct t} :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => is_value' n v && negb (is_error_b v)
    | Constant u    => true
    | Error T       => true


    (* Duplication for the termination checker *)
    | Builtin f   => Nat.ltb n (arity f)
    | Apply nv v  => is_value' n v && negb (is_error_b v) && is_value' (S n) nv
    | TyInst nv T => is_value' (S n) nv
    | _ => false
  end
  .

Definition is_value := is_value' 0.

Fixpoint is_neutral_value (n : nat) (t : Term) :=
  match t with
    | Builtin f   => is_value' n t
    | Apply nv v  => is_value' n t
    | TyInst nv T => is_value' n t
    | _           => false
  end.

Lemma is_value_value : forall t, is_value t = true -> value t.
Admitted.

Lemma is_neutral_value_neutral_value : forall n t, is_neutral_value n t = true -> neutral_value n t.
Admitted.
