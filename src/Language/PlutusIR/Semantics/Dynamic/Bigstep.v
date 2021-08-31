Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Substitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.Values.



(** * Big-step operational semantics *)

(** ** Implementation of big-step semantics as an inductive datatype *)
Reserved Notation "t '==>' v"(at level 40).
Inductive eval : Term -> Term -> Prop :=
  | E_Let : forall bs t v,
      eval_bindings_nonrec (Let NonRec bs t) v ->
      (Let NonRec bs t) ==> v
  | E_LetRec : forall bs t,
      (Let Rec bs t) ==> (Let Rec bs t) (* TODO *)
  (* | E_Var : should never occur *)
  | E_TyAbs : forall X K t v,
      t ==> v ->
      TyAbs X K t ==> TyAbs X K v
  | E_LamAbs : forall x T t,
      LamAbs x T t ==> LamAbs x T t
  | E_Apply : forall t1 t2 x T t0 t0' v2 v0,
      t1 ==> LamAbs x T t0 ->
      t2 ==> v2 ->
      substitute x v2 t0 t0' ->
      t0' ==> v0 ->
      Apply t1 t2 ==> v0
  | E_Constant : forall a,
      Constant a ==> Constant a
  (* Builtins *)
  | E_Builtin : forall f,
      Builtin f ==> Builtin f
  | E_ApplyBuiltin1 : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      value_builtin v1 ->
      t2 ==> v2 ->
      value_builtin (Apply v1 v2) ->
      Apply t1 t2 ==> Apply v1 v2
  | E_ApplyBuiltin2 : forall t1 t2 v1 v2 v0,
      t1 ==> v1 ->
      value_builtin v1 ->
      t2 ==> v2 ->
      ~(value_builtin (Apply v1 v2)) ->
      compute_defaultfun (Apply v1 v2) = Datatypes.Some v0 ->
      Apply t1 t2 ==> v0
  | E_TyInstBuiltin1 : forall t1 T,
      t1 ==> Builtin IfThenElse ->
      TyInst t1 T ==> TyInst (Builtin IfThenElse) T
  (* Type instantiation *)
  | E_TyInst : forall t1 T2 X K v0,
      t1 ==> TyAbs X K v0 ->
      TyInst t1 T2 ==> v0
  (* Errors and their propagation *)
  | E_Error : forall T,
      Error T ==> Error T
  (* Wrap and unwrap *)
  | E_IWrap : forall F T t0 v0,
      t0 ==> v0 ->
      IWrap F T t0 ==> IWrap F T v0
  | E_Unwrap : forall t0 F T v0,
      t0 ==> IWrap F T v0 ->
      Unwrap t0 ==> v0
  (* TODO: Should there be a rule for type reduction? *)

  (* TODO: Errors propagate *)

with eval_bindings_nonrec : Term -> Term -> Prop :=
  | E_NilB_NonRec : forall t v,
      t ==> v ->
      eval_bindings_nonrec (Let NonRec nil t) v
  | E_ConsB_NonRec : forall s x T tb bs t vb bs' t' v,
      tb ==> vb ->
      substitute_bindings_nonrec x vb bs bs' ->
      substitute x vb t t' ->
      eval_bindings_nonrec (Let NonRec bs' t') v ->
      eval_bindings_nonrec (Let NonRec ((TermBind s (VarDecl x T) tb) :: bs) t) v

where "t '==>' v" := (eval t v).

Scheme eval__ind := Minimality for eval Sort Prop
  with eval_bindings_nonrec__ind := Minimality for eval_bindings_nonrec Sort Prop.


(** ** Examples for derivations of [eval] *)

Definition Ty_int : Ty := Ty_Builtin (Some (TypeIn DefaultUniInteger)).
Definition int_to_int : Ty := Ty_Fun Ty_int Ty_int.

Import ZArith.BinInt.
Local Open Scope Z_scope.

Example test_addInteger : forall x,
  Apply (LamAbs x int_to_int (Apply (Var x) (constInt 17))) (Apply (Builtin AddInteger) (constInt 3))
  ==> constInt 20.
Proof.
  intros.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyBuiltin1.
    + apply E_Builtin.
    + apply V_Builtin0.
      simpl.
      apply le_S.
      apply le_n.
    + apply E_Constant.
    + apply V_Builtin1.
      * simpl.
        apply le_n.
      * apply V_Constant.
  - apply S_Apply.
    + apply S_Var1.
    + apply S_Constant.
  - eapply E_ApplyBuiltin2.
    + eapply E_ApplyBuiltin1.
      * apply E_Builtin.
      * apply V_Builtin0.
        simpl.
        apply le_S.
        apply le_n.
      * apply E_Constant.
      * apply V_Builtin1.
        -- simpl.
           apply le_n.
        -- apply V_Constant.
    + apply V_Builtin1.
      -- apply le_n.
      -- apply V_Constant.
    + apply E_Constant.
    + intros Hcon.
      inversion Hcon. subst.
      simpl in H2.
      apply PeanoNat.Nat.lt_irrefl in H2.
      inversion H2. 
    +  reflexivity.
Qed.

Definition int_and_int_to_int : Ty := Ty_Fun Ty_int (Ty_Fun Ty_int Ty_int).


Example test_ifThenElse : forall x y,
  Apply (LamAbs x int_and_int_to_int (Apply (Apply (Var x) (constInt 17)) (constInt 3))) (Apply (TyInst (Apply (LamAbs y Ty_int (Builtin IfThenElse)) (constInt 666)) (Ty_Builtin (Some (TypeIn DefaultUniInteger)))) (Constant (Some (ValueOf DefaultUniBool true)))) ==> constInt 17.
Proof.
  intros.
  eapply E_Apply.
  - apply E_LamAbs.
  - eapply E_ApplyBuiltin1.
    + eapply E_TyInstBuiltin1. 
      eapply E_Apply.
      * apply E_LamAbs.
      * apply E_Constant.
      * apply S_Builtin.
      * apply E_Builtin.
    + apply V_Builtin1_WithTyInst.
      simpl. apply le_S. apply le_S. apply le_n.
    + apply E_Constant.
    + apply V_Builtin2_WithTyInst.
      * simpl. apply le_S. apply le_n.
      * apply V_Constant.
  - apply S_Apply.
    + apply S_Apply.
      * apply S_Var1.
      * apply S_Constant.
    + apply S_Constant.
  - eapply E_ApplyBuiltin2.
    + apply E_ApplyBuiltin1.
      * apply E_ApplyBuiltin1.
        -- apply E_TyInstBuiltin1.
           apply E_Builtin.
        -- apply V_Builtin1_WithTyInst.
           simpl. apply le_S. apply le_S. apply le_n.
        -- apply E_Constant.
        -- apply V_Builtin2_WithTyInst.
           ++ simpl. apply le_S. apply le_n.
           ++ apply V_Constant.
      * apply V_Builtin2_WithTyInst.
        -- simpl. apply le_S. apply le_n.
        -- apply V_Constant.
      * apply E_Constant.
      * apply V_Builtin3_WithTyInst.
        -- simpl. apply le_n.
        -- apply V_Constant.
        -- apply V_Constant.
    + apply V_Builtin3_WithTyInst.
      * simpl. apply le_n.
      * apply V_Constant.
      * apply V_Constant.
    + apply E_Constant.
    + intros Hcon.
      inversion Hcon.
    + reflexivity.
Qed.