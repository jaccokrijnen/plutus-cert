Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import
  Equality
  Builtins.Arity
.
From Coq Require Import
  Lists.List
  Bool.Bool
  Arith.PeanoNat
  Program.Equality
.
Import PeanoNat.Nat.

Inductive is_error : term -> Prop :=
  | IsError : forall T,
      is_error (Error T).

Fixpoint arg_count (t : term) : nat :=
  match t with
  | Apply s t => 1 + arg_count s
  | TyInst t T => 1 + arg_count t
  | _ => 0
  end
.

Inductive value : term -> Prop :=
  | V_LamAbs : forall x T t0,
      value (LamAbs x T t0)
  | V_TyAbs : forall X K t,
      value (TyAbs X K t)
  | V_IWrap : forall F T v,
      value v ->
      value (IWrap F T v)
  | V_Constant : forall u,
      value (Constant u)
  | V_Constr : forall T i vs,
      Forall value vs ->
      value (Constr T i vs)
  | V_AppliedBuiltin : forall f t,
      arg_count t < arity f ->
      applied f t ->
      value t

with applied : DefaultFun -> term -> Prop :=
  | A_Builtin : forall f,
      applied f (Builtin f)
  | A_Apply : forall f t v,
      value v ->
      applied f t ->
      applied f (Apply t v)
  | A_TyInst : forall f t T,
      applied f t ->
      applied f (TyInst t T)
  .

#[export] Hint Constructors value applied : core.

Section value_ind.
Context
  (P : term -> Prop)
  (Q : DefaultFun -> term -> Prop)
.
Context
  (H_LamAbs : forall (x : String.string) (T : ty) (t0 : term), P (LamAbs x T t0))
  (H_TyAbs : forall (X : String.string) (K : kind) (t : term), P (TyAbs X K t))
  (H_IWrap : forall (F T : ty) (v : term), value v -> P v -> P (IWrap F T v))
  (H_Constant : forall c : constant, P (Constant c))
  (H_Constr : forall (T : ty) (i : nat) (vs : list term), Forall value vs -> Forall P vs -> P (Constr T i vs))
  (H_AppliedBuiltin : forall f t, arg_count t < arity f -> applied f t -> Q f t -> P t)

  (H_Builtin : forall f, Q f (Builtin f))
  (H_Apply : forall f t v, value v -> P v -> applied f t -> Q f t -> Q f (Apply t v))
  (H_TyInst : forall f t T, applied f t -> Q f t -> Q f (TyInst t T))
.

Fixpoint values__ind (H_value : forall (t : term), value t -> P t) (ts : list term) (vs : Forall value ts): Forall P ts :=
  match vs as vs in Forall _ ts return Forall P ts with
    | Forall_nil _ => Forall_nil _
    | @Forall_cons _ _ x xs vx vxs => @Forall_cons _ _ x xs (H_value x vx) (values__ind H_value xs vxs)
  end.

Fixpoint value__ind (t : term) (v : value t) {struct v} : P t :=
  match v in (value t0) return (P t0) with
  | V_LamAbs x T t0 => H_LamAbs x T t0
  | V_TyAbs X K t0 => H_TyAbs X K t0
  | V_IWrap F1 T v0 v1 => H_IWrap F1 T v0 v1 (value__ind v0 v1)
  | V_Constant u => H_Constant u
  | V_Constr T i ts vs => H_Constr T i ts vs
      ((fix F ts vs := match vs as vs in Forall _ ts return Forall P ts with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ t ts vt vts => @Forall_cons _ _ t ts (value__ind t vt) (F ts vts)
      end) ts vs)
  | V_AppliedBuiltin f t H_arity app => H_AppliedBuiltin f t H_arity app (applied__ind f t app)
  end
with applied__ind f t (H_a : applied f t) {struct H_a} : Q f t :=
  match H_a in (applied f0 t0) return (Q f0 t0) with
  | A_Builtin f => H_Builtin f
  | A_Apply f t v H_val H_a => H_Apply f t v H_val (value__ind v H_val) H_a (applied__ind f t H_a)
  | A_TyInst f t T H_a => H_TyInst f t T H_a (applied__ind f t H_a)
  end
.

End value_ind.

Inductive result' : term -> Prop :=
  | R'_Value t : value t -> result' t
  | R'_Error T : result' (Error T)
.

(* Results represent the result of computation, which include values and errors *)
Inductive result : term -> Prop :=
  | R_LamAbs : forall x T t0,
      result (LamAbs x T t0)
  | R_TyAbs : forall X K t,
      result (TyAbs X K t)
  | R_IWrap : forall F T v,
      result v ->
      ~ is_error v ->
      result (IWrap F T v)
  | R_Constant : forall u,
      result (Constant u)
  | R_Error : forall T,
      result (Error T)
  | R_Constr : forall T i vs,
      Forall result vs ->
      result (Constr T i vs)
  .

#[export] Hint Constructors result : core.

Section result_ind.
Context
  (P : term -> Prop)
.
Context
  (H_LamAbs : forall (x : String.string) (T : ty) (t0 : term), P (LamAbs x T t0))
  (H_TyAbs : forall (X : String.string) (K : kind) (t : term), P (TyAbs X K t))
  (H_IWrap : forall (F T : ty) (v : term), result v -> P v -> ~ is_error v -> P (IWrap F T v))
  (H_Constant : forall c : constant, P (Constant c))
  (H_Error : forall T : ty, P (Error T))
  (H_Constr : forall (T : ty) (i : nat) (vs : list term), Forall result vs -> Forall P vs -> P (Constr T i vs))
.
Fixpoint results__ind (H_result : forall (t : term), result t -> P t) (ts : list term) (vs : Forall result ts): Forall P ts :=
  match vs as vs in Forall _ ts return Forall P ts with
    | Forall_nil _ => Forall_nil _
    | @Forall_cons _ _ x xs vx vxs => @Forall_cons _ _ x xs (H_result x vx) (results__ind H_result xs vxs)
  end.
Fixpoint result__ind (t : term) (v : result t) {struct v} : P t :=
  match v in (result t0) return (P t0) with
  | R_LamAbs x T t0 => H_LamAbs x T t0
  | R_TyAbs X K t0 => H_TyAbs X K t0
  | R_IWrap F1 T v0 v1 n => H_IWrap F1 T v0 v1 (result__ind v0 v1) n
  | R_Constant u => H_Constant u
  | R_Error T => H_Error T
  | R_Constr T i ts vs => H_Constr T i ts vs
      ((fix F ts vs := match vs as vs in Forall _ ts return Forall P ts with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ t ts vt vts => @Forall_cons _ _ t ts (result__ind t vt) (F ts vts)
      end) ts vs)
  end
.

End result_ind.


Lemma value__is_error v : value v -> ~ is_error v.
Proof.
  intros H.
  induction v;
  inversion H;
  inversion 1.
  (* Applied builtin *)
  inversion H1.
Qed.

Lemma value__result' v : value v -> result' v.
Proof. auto using result'. Qed.

Lemma value__result v : value v -> result v.
Admitted.

Lemma result'__value v : result' v -> ~ is_error v -> value v.
Admitted.

Lemma result__value v : result v -> ~ is_error v-> value v.
Admitted.

Lemma is_error_dec t : {is_error t} + {~ is_error t}.
Proof.
  destruct t.
  all: try (solve [right; inversion 1 | left; constructor]).
Defined.

Lemma ForallT_dec {A} (P : A -> Prop) (xs : list A) :
 Util.ForallT (fun x => {P x} + {~ P x}) xs ->
 {Forall P xs} + {~ (Forall P xs)}.
Proof.
  intros H.
  induction H.
  - left. constructor.
  - destruct IHForallT, p.
    all: try solve [right; inversion 1; contradiction].
    left. auto.
Defined.

Lemma value_dec t : {value t} + {~ value t}.
Admitted.

Lemma result'_dec t : {result' t} + {~ result' t}.
Admitted.

Lemma result_dec t : {result t} + {~ result t}.
Proof.
  apply term__rect with
    (P := fun t => {result t} + {~result t})
    (Q := fun b => unit).
  all: intros.
  all: try solve
    [ right; inversion 1
    | left; constructor
    | exact tt ].
  - (* IWrap *)
    destruct (is_error_dec t2).
    + right; inversion 1; contradiction.
    + destruct H.
      * left. constructor; auto.
      * right. inversion 1; contradiction.
  - (* Constr *)
    apply ForallT_dec in X.
    destruct X.
    + left. auto.
    + right. inversion 1. contradiction .
Defined.



Definition is_error_beq (t : term) : bool :=
  match t with
    | Error _ => true
    | _       => false
  end.

Fixpoint value_beq (t : term) : bool.
Admitted.

Fixpoint result'_beq (t : term) : bool.
Admitted.

Fixpoint result_beq (t : term) :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => result_beq v && negb (is_error_beq v)
    | Constant u    => true
    | Error T       => true
    | _ => false
  end
  .

Lemma value_beq__value : forall t, value_beq t = true <-> value t.
Admitted.
Lemma result'_dec__result' : forall t, result'_beq t = true <-> result' t.
Admitted.

Lemma dec_result_result : forall t, result_beq t = true -> result t.
Admitted.

