Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.AnnotationSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.



Create HintDb smallstep_db.

Reserved Notation "t '-->' t'" (at level 40).


Inductive step : Term -> Term -> Prop :=
  (* Let-bindings *)
  | ST_Let_NilB : forall recty t,
      Let recty nil t --> t
  | ST_LetNonRec_ConsB1 : forall s x T tb bs t tb',
      tb --> tb' ->
      Let NonRec ((TermBind s (VarDecl x T) tb) :: bs) t -->
        Let NonRec ((TermBind s (VarDecl x T) tb') :: bs) t
  | ST_LetNonRec_ConsB2 :  forall s x T vb bs t bs' t',
      value vb ->
      substitute x vb (Let NonRec bs t) (Let NonRec bs' t') ->
      Let NonRec ((TermBind s (VarDecl x T) vb) :: bs) t --> Let NonRec bs' t'
  (* Apply *)
  | ST_Apply1 : forall t1 t1' t2,
      t1 --> t1' ->
      Apply t1 t2 --> Apply t1' t2
  | ST_Apply2 : forall x T t0 t2 t2',
      t2 --> t2' ->
      Apply (LamAbs x T t0) t2 --> Apply (LamAbs x T t0) t2'
  | ST_ApplyLamAbs : forall x T t0 v2 t0',
      value v2 ->
      substitute x v2 t0 t0' ->
      Apply (LamAbs x T t0) v2 --> t0'
  (* Builtins *)
  | ST_Apply3 : forall v1 t2 t2',
      value_builtin v1 ->
      t2 --> t2' ->
      Apply v1 t2 --> Apply v1 t2' 
  | ST_ApplyBuiltin : forall v1 v2 v0,
      value_builtin v1 ->
      value v2 ->
      ~(value_builtin (Apply v1 v2)) ->
      compute_defaultfun (Apply v1 v2) = Datatypes.Some v0 ->
      Apply v1 v2 --> v0
  (* If-Then-Else *)
  | ST_ApplyIf : forall cond cond' T then_branch else_branch,
      cond --> cond' ->
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) cond) then_branch) else_branch --> Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) cond') then_branch) else_branch
  | ST_ApplyIfTrue : forall T then_branch else_branch,
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) then_branch) else_branch --> then_branch
  | ST_ApplyIfFalse : forall T then_branch else_branch, 
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) then_branch) else_branch --> else_branch

  (* TyInst *)
  | ST_TyInst1 : forall t1 t1' T,
      t1 --> t1' ->
      TyInst t1 T --> TyInst t1' T
  | ST_TyInstTyAbs : forall X K v0 T v0',
      substituteA X T v0 v0' ->
      TyInst (TyAbs X K v0) T --> v0' 

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
  | ST_Apply1_Error : forall T_err t1 t2,
      t1 --> Error T_err ->
      Apply t1 t2 --> Error T_err
  | ST_Apply2_Error : forall T_err x T t0 t2,
      t2 --> Error T_err ->
      Apply (LamAbs x T t0) t2 --> Error T_err
  | ST_Apply3_Error : forall T_err v1 t2,
      value_builtin v1 ->
      t2 --> Error T_err ->
      Apply v1 t2 --> Error T_err
  | ST_ApplyIf_Error : forall cond T T_err then_branch else_branch,
      cond --> Error T_err ->
      Apply (Apply (Apply (TyInst (Builtin IfThenElse) T) cond) then_branch) else_branch --> Error T_err
  | ST_TyInst1_Error : forall t1 T T_err,
      t1 --> Error T_err ->
      TyInst t1 T --> Error T_err
  | ST_IWrap_Error : forall F T t0 T_err,
      t0 --> Error T_err ->
      IWrap F T t0 --> Error T_err
  | ST_Unwrap_Error : forall t0 T_err,
      t0 --> Error T_err ->
      Unwrap t0 --> Error T_err

where "t '-->' t'" := (step t t').

#[export] Hint Constructors step : smallstep_db.

(* Multistep reduction *)

(* multi is equivalent to refl_trans_clos_1n, but I could not get it to work by just using refl_trans_clos_1n. *)
Inductive multi {X : Type} (R : X -> X -> Prop) (x : X) : X -> Prop :=
  | multi_refl : multi R x x
  | multi_step : forall (y z : X), R x y -> multi R y z -> multi R x z
.

Notation multistep := (multi step).

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

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