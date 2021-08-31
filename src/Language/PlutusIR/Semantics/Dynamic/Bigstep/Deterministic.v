Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
(** * [substitute] is deterministic*)

Definition P_substitute (x : name) (s t t' : Term) : Prop :=
  forall t'',
    substitute x s t t'' ->
    t' = t''. 

Definition P_substitute_bindings_nonrec (x : name) (s : Term) (bs bs' : list Binding) : Prop :=
  forall bs'',
    substitute_bindings_nonrec x s bs bs'' ->
    bs' = bs''.

Definition P_substitute_bindings_rec (x : name) (s : Term) (bs bs' : list Binding) : Prop :=
  forall bs'',
    substitute_bindings_rec x s bs bs'' ->
    bs' = bs''.
        
Definition P_substitute_binding (x : name) (s : Term) (b b' : Binding) : Prop :=
  forall b'',
    substitute_binding x s b b'' ->
    b' = b''.

Theorem substitute__deterministic : 
  (forall x s t t', substitute x s t t' -> P_substitute x s t t') /\
  (forall x s bs bs', substitute_bindings_nonrec x s bs bs' -> P_substitute_bindings_nonrec x s bs bs') /\
  (forall x s bs bs', substitute_bindings_rec x s bs bs' -> P_substitute_bindings_rec x s bs bs') /\
  (forall x s b b', substitute_binding x s b b' -> P_substitute_binding x s b b').
Proof.
  apply substitute__mutind with 
    (P := P_substitute)
    (P0 := P_substitute_bindings_nonrec)
    (P1 := P_substitute_bindings_rec)
    (P2 := P_substitute_binding). 
  - (* S_Let1 *)
    intros. unfold P_substitute. intros.
    inversion H2.
    + subst.
      assert (bs' = bs'0) by auto.
      subst.
      reflexivity.
    + subst.
      apply H5 in H.
      destruct H.
  - (* S_Let2 *)
    intros. unfold P_substitute. intros.
    inversion H4.
    + subst.
      apply H in H9.
      destruct H9.
    + subst.
      assert (bs' = bs'0) by auto.
      subst.
      assert (t0' = t0'0) by auto.
      subst.
      reflexivity.
  - (* S_LetRec1 *)
    intros. unfold P_substitute. intros.
    inversion H0.
    + subst.
      reflexivity.
    + subst.
      apply H3 in H.
      destruct H.
  - (* S_LetRec2 *)
    intros. unfold P_substitute. intros.
    inversion H4. 
    + subst.
      apply H in H10.
      destruct H10.
    + subst.
      assert (bs' = bs'0) by auto.
      subst.
      assert (t0' = t0'0) by auto.
      subst.
      reflexivity.
  - (* S_Var1 *)
    intros. unfold P_substitute. intros.
    inversion H. 
    + subst.
      reflexivity.
    + subst.
      assert (x = x) by reflexivity.
      apply H3 in H0.
      destruct H0.
  - (* S_Var2 *)
    intros. unfold P_substitute. intros.
    inversion H0. subst.
    + subst.
      assert (y = y) by reflexivity.
      apply H in H1.
      destruct H1.
    + subst.
      reflexivity.
  - (* S_TyAbs *)
    intros. unfold P_substitute. intros. 
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_LamAbs1 *)
    intros. unfold P_substitute. intros.
    inversion H.
    + subst.
      reflexivity.
    + subst.
      assert (x = x) by auto.
      apply H6 in H0.
      destruct H0.
  - (* S_LamAbs2 *)
    intros. unfold P_substitute. intros.
    inversion H2. 
    + subst.
      assert (bx = bx) by auto.
      apply H in H3.
      destruct H3.
    + subst.
      assert (t0' = t0'0) by auto.
      subst.
      reflexivity.
  - (* S_Apply *)
    intros. unfold P_substitute. intros.
    inversion H3. subst.
    assert (t1' = t1'0) by auto.
    assert (t2' = t2'0) by auto.
    subst.
    reflexivity.
  - (* S_Constant *)
    intros. unfold P_substitute. intros.
    inversion H. subst.
    reflexivity.
  - (* S_Builtin *)
    intros. unfold P_substitute. intros.
    inversion H. subst.
    reflexivity.
  - (* S_TyInst *)
    intros. unfold P_substitute. intros.
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_Error *)
    intros. unfold P_substitute. intros.
    inversion H. subst.
    reflexivity.
  - (* S_IWrap *)
    intros. unfold P_substitute. intros.
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_Unwrap *)
    intros. unfold P_substitute. intros.
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  
  - (* S_NilB_NonRec *)
    intros. unfold P_substitute_bindings_nonrec. intros.
    inversion H. subst.
    reflexivity.
  - (* S_ConsB_NonRec1 *)
    intros. unfold P_substitute_bindings_nonrec. intros.
    inversion H2.
    + subst.
      assert (b' = b'0) by auto.
      subst.
      reflexivity.
    + subst.
      apply H5 in H.
      destruct H.
  - (* S_ConsB_NonRec2 *)
    intros. unfold P_substitute_bindings_nonrec. intros.
    inversion H4.
    + subst.
      apply H in H9.
      destruct H9.
    + subst.
      assert (b' = b'0) by auto.
      assert (bs' = bs'0) by auto.
      subst.
      reflexivity.

  - (* S_NilB_Rec *)
    intros. unfold P_substitute_bindings_rec. intros.
    inversion H. subst.
    reflexivity. 
  - (* S_ConsB_Rec *)
    intros. unfold P_substitute_bindings_rec. intros.
    inversion H3. subst.
    assert (b' = b'0) by auto.
    assert (bs' = bs'0) by auto.
    subst.
    reflexivity.
  
  - (* S_TermBind *)
    intros. unfold P_substitute_binding. intros.
    inversion H1. subst.
    assert (t' = t'0) by auto.
    subst.
    reflexivity.
  - (* S_TypeBind *)
    intros. unfold P_substitute_binding. intros.
    inversion H. subst.
    reflexivity.
  - (* S_DatatypeBind *)
    intros. unfold P_substitute_binding. intros.
    inversion H. subst.
    reflexivity.
Qed.

(** * [eval] is deterministic *)

Definition P_eval x y1 :=
  forall y2,
    x ==> y2 ->
    y1 = y2.

Definition P_eval_bindings_nonrec x y1 :=
  forall y2,
    eval_bindings_nonrec x y2 ->
    y1 = y2.

Definition P_eval_bindings_rec bs0 x y1 :=
  forall y2,
    eval_bindings_rec bs0 x y2 ->
    y1 = y2.

Theorem eval__deterministic : forall x y1,
  x ==> y1 ->
  P_eval x y1.
Proof.
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec).
  - (* E_Let *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    apply H0.
    assumption.
  - (* E_LetRec *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    apply H0.
    assumption.
  - (* E_TyAbs *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    f_equal.
    apply H0.
    assumption.
  - (* E_LamAbs *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
  - (* E_Apply *)
    intros. unfold P_eval. intros.
    inversion H6.
    + (* E_Apply *)
      subst.
      apply H5.
      assert (LamAbs x T t0 = LamAbs x0 T0 t5). {
        apply H0. assumption.
      }
      inversion H7. subst.
      assert (v2 = v1). {
        apply H2. assumption.
      }
      subst.
      assert (t0'0 = t0'). {
        apply substitute__deterministic with x0 v1 t5.
        + assumption.
        + assumption.
      }
      subst. 
      assumption.
    + (* E_ApplyBuiltin1 *)
      subst.
      assert (LamAbs x T t0 = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H13.
    + (* E_ApplyBuiltin2 *) 
      subst. 
      assert (LamAbs x T t0 = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H10.
    + (* E_IfCondition*)
      subst.
      assert (LamAbs x T t0 = TyInst (Builtin IfThenElse) T0). {
        apply H0. assumption.
      }
      inversion H7.
    + (* E_IfThenBranch *)
      subst.
      assert (LamAbs x T t0 = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        apply H0. assumption.
      }
      inversion H7.
    + (* E_IfTrue *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        apply H0. assumption.
      }
      inversion H7.
    + (* E_IfFalse *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        apply H0. assumption.
      }
      inversion H7.
  - (* E_Constant *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
  - (* E_Builtin *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
  - (* E_ApplyBuiltin1 *)
    intros. unfold P_eval. intros.
    inversion H5.
    + (* E_Apply *) 
      subst.
      assert (v1 = LamAbs x T t4). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
    + (* E_AppltBuiltin1 *)
      subst.
      assert (v1 = v0). {
        apply H0. assumption.
      }
      subst.
      assert (v2 = v3). {
        apply H3. assumption.
      }
      subst.
      reflexivity.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (v1 = v0). {
        apply H0. assumption.
      }
      subst.
      assert (v2 = v3). {
        apply H3. assumption.
      }
      subst.
      apply H11 in H4.
      destruct H4.
    + (* E_IfCondition*)
      subst.
      assert (v1 = TyInst (Builtin IfThenElse) T). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (v1 = Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
    + (* E_IfFalse *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
  - (* E_ApplyBuiltin2 *)
    intros. unfold P_eval. intros.
    inversion H6. subst.
    + (* E_Apply *) 
      subst.
      assert (v1 = LamAbs x T t4). {
        apply H0. assumption.
      }
      subst.
      inversion H1.
    + (* E_ApplyBuiltin1 *)
      subst.
      assert (v1 = v3). {
        apply H0. assumption.
      }
      subst.
      assert (v2 = v4). {
        apply H3. assumption.
      }
      subst.
      apply H4 in H13.
      destruct H13.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (v1 = v3). {
        apply H0. assumption.
      }
      subst.
      assert (v2 = v4). {
        apply H3. assumption.
      }
      subst. 
      rewrite H5 in H14. 
      inversion H14. 
      subst. 
      reflexivity.
    + (* E_IfCondition*)
      subst.
      assert (v1 = TyInst (Builtin IfThenElse) T). {
        apply H0. assumption.
      }
      subst.
      inversion H1.
    + (* E_IfThenBranch *)
      subst.
      assert (v1 = Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        apply H0. assumption.
      }
      subst.
      inversion H1.
    + (* E_IfTrue *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H1.
    + (* E_IfFalse *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H1.
  - (* E_IfTyInst *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_IfTyInst *)
      reflexivity.
    + (* E_TyInst *)  
      subst.
      assert (Builtin IfThenElse = TyAbs X K y2). {
        apply H0. assumption.
      }
      inversion H2.
  - (* E_IfCondition *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (TyInst (Builtin IfThenElse) T = LamAbs x T0 t0). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (TyInst (Builtin IfThenElse) T = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H7.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (TyInst (Builtin IfThenElse) T = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      f_equal.
      * apply H0. assumption.
      * apply H2. assumption.
    + (* E_IfThenBranch *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond0)))). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
    + (* E_IfFalse *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        apply H0. assumption.
      }
      subst.
      inversion H4.
  - (* E_IfThenBranch *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_Apply *) 
      subst.
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = LamAbs x T0 t0). {
        apply H0. assumption.
      }
      inversion H2.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H8.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H5.
    + (* E_IfCondition*)
      subst.
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = (TyInst (Builtin IfThenElse) T0)). {
        apply H0. assumption.
      }
      inversion H2.
    + (* E_IfThenBranch *)
      subst.
      f_equal.
      apply H0. assumption.
    + (* E_IfTrue *)
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        apply H0. assumption.
      }
      subst.
      inversion H7.
    + (* E_IfFalse *)
      subst.
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        apply H0. assumption.
      }
      inversion H2.
  - (* E_IfTrue *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = LamAbs x T0 t0). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H10.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = (TyInst (Builtin IfThenElse) T0)). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        apply H0. assumption.
      }
      inversion H4.
      subst.
      apply H2.
      assumption.
    + (* E_IfFalse *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        apply H0. assumption.
      }
      inversion H4.
      Axiom skip : forall P, P. apply skip. (* TODO: Why does inversion not do anything? *)
  - (* E_IfFalse *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = LamAbs x T0 t0). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H10.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = v1). {
        apply H0. assumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = (TyInst (Builtin IfThenElse) T0)). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        apply H0. assumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        apply H0. assumption.
      }
      inversion H4.
      apply skip. (* TODO: Why does inversion not do anything? *)

    + (* E_IfFalse *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        apply H0. assumption.
      }
      inversion H4.
      subst.
      apply H2.
      assumption.
  - (* E_TyInst *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_IfTyInst *)
      subst.
      assert (TyAbs X K v0 = Builtin IfThenElse). {
        apply H0. assumption.
      }
      inversion H2.
    + (* E_TyInst *)
      subst.
      assert (TyAbs X K v0 = TyAbs X0 K0 y2). {
        apply H0. assumption.
      }
      inversion H2. subst.
      reflexivity.
  - (* E_Error *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
  - (* E_IWrap *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    f_equal.
    apply H0.
    assumption.
  - (* E_Unwrap *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    assert (IWrap F T v0 = IWrap F0 T0 y2). {
      apply H0. assumption.  
    }
    inversion H2. subst.
    reflexivity.
  
  - (* E_NilB_NonRec  *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H1. subst.
    apply H0. assumption.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H5. subst.
    assert (vb = vb0). {
      apply H0. assumption.
    }
    subst.
    assert (t' = t'0). {
      apply substitute__deterministic in H2.
      apply H2 in H15.
      assumption.
    }
    subst.
    assert (bs' = bs'0). {
      apply substitute__deterministic in H1.
      apply H1 in H14.
      assumption.
    }
    subst.
    apply H4.
    assumption.
  
  - (* E_NilB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H1. subst.
    apply H0.
    assumption.
  - (* E_ConsB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H2. subst.
    assert (t' = t'0). {
      apply substitute__deterministic in H.
      apply H in H11.
      assumption.
    }
    subst.
    apply H1.
    assumption.
Qed.