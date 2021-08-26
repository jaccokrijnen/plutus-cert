Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.



Create HintDb smallstep_db.

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : Term -> Term -> Prop :=
  (* Let-bindings *)
  | ST_Let : forall bs t t',
      step_bindings_nonrec (Let NonRec bs t) t' ->
      step (Let NonRec bs t) t'
  (* TyAbs *)
  | ST_TyAbs : forall X K t t',
      t --> t' ->
      TyAbs X K t --> TyAbs X K t'

  (* Apply *)
  | ST_Apply1 : forall t1 t1' t2,
      t1 --> t1' ->
      Apply t1 t2 --> Apply t1' t2
  | ST_Apply2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      Apply v1 t2 --> Apply v1 t2'
  | ST_ApplyLamAbs : forall x T t0 v2 t0',
      value v2 ->
      substitute x v2 t0 t0' ->
      Apply (LamAbs x T t0) v2 --> t0'
  (* Builtins *)
  | ST_ApplyBuiltin2 : forall v1 v2 v0,
      value_builtin v1 ->
      value v2 ->
      ~(value_builtin (Apply v1 v2)) ->
      compute_defaultfun (Apply v1 v2) = Datatypes.Some v0 ->
      Apply v1 v2 --> v0

  (* TyInst *)
  | ST_TyInst1 : forall t1 t1' T,
      t1 --> t1' ->
      TyInst t1 T --> TyInst t1' T
  | ST_TyInstTyAbs : forall X K v0 T,
      TyInst (TyAbs X K v0) T --> v0 

  (* Wrap and unwrap *)
  | ST_IWrap : forall F T t0 t0',
      t0 --> t0' ->
      IWrap F T t0 --> IWrap F T t0'
  | ST_Unwrap1 : forall t0 t0',
      t0 --> t0' ->
      Unwrap t0 --> Unwrap t0'
  | ST_UnwrapWrap : forall F T v0,
      Unwrap (IWrap F T v0) --> v0

  (* Errors *)

with step_bindings_nonrec : Term -> Term -> Prop :=
  | ST_NilB_NonRec1 : forall t t',
      t --> t' ->
      step_bindings_nonrec (Let NonRec nil t) (Let NonRec nil t')
  | ST_NilB_NonRec2 : forall v,
      value v ->
      step_bindings_nonrec (Let NonRec nil v) v
  | ST_ConsB_NonRec1 : forall s x T tb bs t tb',
      tb --> tb' ->
      step_bindings_nonrec (Let NonRec ((TermBind s (VarDecl x T) tb) :: bs) t) (Let NonRec ((TermBind s (VarDecl x T) tb') :: bs) t)
  | ST_ConsB_NonRec2 : forall s x T vb bs t bs' t',
      value vb ->
      substitute_bindings_nonrec x vb bs bs' ->
      substitute x vb t t' ->
      step_bindings_nonrec (Let NonRec ((TermBind s (VarDecl x T) vb) :: bs) t) (Let NonRec bs' t')

where "t '-->' t'" := (step t t').

#[export] Hint Constructors step : smallstep_db.
#[export] Hint Constructors step_bindings_nonrec : smallstep_db.

(* Multistep reduction *)

(* multi is equivalent to refl_trans_clos_1n, but I could not get it to work by just using refl_trans_clos_1n. *)
Inductive multi {X : Type} (R : X -> X -> Prop) (x : X) : X -> Prop :=
  | multi_refl : multi R x x
  | multi_step : forall (y z : X), R x y -> multi R y z -> multi R x z
.

Notation multistep := (multi step).

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation multistepBNR := (multi step_bindings_nonrec).

#[export] Hint Constructors multi : smallstep_db.

(* **** Properties *)

Theorem multi_R : forall (X : Type) (R : X -> X -> Prop) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros.
  eapply multi_step.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans : forall (X : Type) (R : X -> X -> Prop) (x y z : X),
    multi R x y ->
    multi R y z ->
    multi R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy.
  - apply Hyz.
  - eapply multi_step.
    + apply H.
    + apply IHHxy.
      assumption.
Qed.

#[export] Hint Resolve multi_R multi_trans : smallstep_db.