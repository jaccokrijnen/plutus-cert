Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import
  Equality
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
  .

#[export] Hint Constructors value : core.

Section value_ind.
Context
  (P : term -> Prop)
.
Context
  (H_LamAbs : forall (x : String.string) (T : ty) (t0 : term), P (LamAbs x T t0))
  (H_TyAbs : forall (X : String.string) (K : kind) (t : term), P (TyAbs X K t))
  (H_IWrap : forall (F T : ty) (v : term), value v -> P v -> ~ is_error v -> P (IWrap F T v))
  (H_Constant : forall c : constant, P (Constant c))
  (H_Error : forall T : ty, P (Error T))
  (H_Constr : forall (i : nat) (T : ty) (vs : list term), Forall value vs -> Forall P vs -> P (Constr i T vs))
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
  | V_IWrap F1 T v0 v1 n => H_IWrap F1 T v0 v1 (value__ind v0 v1) n
  | V_Constant u => H_Constant u
  | V_Error T => H_Error T
  | V_Constr i T ts vs => H_Constr i T ts vs
      ((fix F ts vs := match vs as vs in Forall _ ts return Forall P ts with
        | Forall_nil _ => Forall_nil _
        | @Forall_cons _ _ t ts vt vts => @Forall_cons _ _ t ts (value__ind t vt) (F ts vts)
      end) ts vs)
  end
.

End value_ind.

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
Proof.
  apply term__rect with
    (P := fun t => {value t} + {~value t})
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

Fixpoint value_beq (t : term) :=
  match t with
    | LamAbs x T t0 => true
    | TyAbs X K t   => true
    | IWrap F T v   => value_beq v && negb (is_error_beq v)
    | Constant u    => true
    | Error T       => true
    | _ => false
  end
  .

Lemma dec_value_value : forall t, value_beq t = true -> value t.
Admitted.
