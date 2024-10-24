Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
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


(* built-in that is applied to values/types of which the (type) arguments match
   the signature *)
Inductive applied_builtin : DefaultFun -> builtin_sig -> term -> Prop :=
  | BA_Builtin : forall f,
      applied_builtin f (to_sig f) (Builtin f)
  | BA_Apply : forall f sig t v T,
      value v ->
      ~ is_error v ->
      applied_builtin f (BS_Fun T sig) t ->
      applied_builtin f sig (Apply t v)
  | BA_TyInst : forall f t T X K sig,
      applied_builtin f (BS_Forall X K sig) t ->
      applied_builtin f sig (TyInst t T)
  .

Lemma applied_builtin__functional f f' s s' t : applied_builtin f s t -> applied_builtin f' s' t -> f = f' /\ s = s'.
Proof.
  revert f f' s s'.
  induction t.
  all: try solve [intros ? ? ? ?; inversion 1].
  - clear IHt2.
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    specialize (IHt1 _ _ _ _ H6 H9) as [H_f H_s].
    inversion H_s.
    subst.
    split; reflexivity.
  -
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    split; reflexivity.
  -
    intros ? ? ? ? H H'.
    inversion H; subst.
    inversion H'; subst.
    specialize (IHt _ _ _ _ H3 H4) as [H_f H_s].
    inversion H_s.
    subst.
    split; reflexivity.
Defined.

Corollary applied_builtin__functional_sig f f' s s' t : applied_builtin f s t -> applied_builtin f' s' t -> s = s'.
Proof.
  intros.
  eapply proj2.
  eauto using applied_builtin__functional.
Defined.

Ltac contradiction_exists :=
  match goal with
  | H  : { _ & {_ & applied_builtin _ _ ?t}} -> False
  , H' : applied_builtin _ _ ?t
  |- _ => apply H; eexists; eexists; apply H'
  end.

Ltac contradict_diff_sigs :=
  match goal with
  | H1 : applied_builtin ?f ?s ?t
  , H2 : applied_builtin ?f' ?s' ?t
  |- _ => assert (H_absurd : s = s') by eauto using applied_builtin__functional_sig; inversion H_absurd
  end.

Ltac fully_strategy := try solve
  [ right;
    let H := fresh "H" in
    destruct 1 as [ ? [? H] ];
    inversion H;
    (contradiction || contradiction_exists || contradict_diff_sigs)
  ]
.


Lemma applied_builtin_dec t :
   {f & {s & applied_builtin f s t}}  +
  ({f & {s & applied_builtin f s t}} -> False).
Proof with fully_strategy.
  induction t...
  - destruct IHt1 as [[ f [ s H' ]] | ], (value_dec t2), (is_error_dec t2)...
    destruct s eqn:H_s...
    left.
    eauto using applied_builtin.
  - left.
    eauto using applied_builtin.
  - destruct IHt as [[ f [ s H' ]] | ]...
    destruct s eqn:H_s...
    left.
    eauto using applied_builtin.
Defined.

Fixpoint result_ty (s : builtin_sig) : ty :=
  match s with
  | BS_Forall _ _ s => result_ty s
  | BS_Fun _ s => result_ty s
  | BS_Result t => t
  end
.


Definition fully_applied t := exists f, applied_builtin f (BS_Result (result_ty (to_sig f))) t.

Lemma fully_applied_dec t : {fully_applied t} + {~fully_applied t}.
Proof.
  destruct (applied_builtin_dec t) as [ H | H ] .
  - destruct H as [ f [ s H_app ]].
    destruct (builtin_sig_eq_dec s (BS_Result (result_ty (to_sig f)))).
    + subst. left. unfold fully_applied. eauto.
    + right. unfold fully_applied. intro H.
      destruct H as [ ? Hb ].
      match goal with
      | H1 : applied_builtin ?f ?s ?t
      , H2 : applied_builtin ?f' ?s' ?t
      |- _ => assert (H_absurd : f = f' /\ s = s') by eauto using applied_builtin__functional
      end.
      destruct H_absurd.
      subst.
      contradiction.
  - right.
    destruct 1 as [ f Happ ].
    apply H.
    eauto.
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
