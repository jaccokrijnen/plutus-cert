Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.

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

Theorem eval_defaultfun__deterministic : forall (t : Term) v1 v2,
  eval_defaultfun t v1 ->
  eval_defaultfun t v2 ->
  v1 = v2.
Proof.
  intros. inversion H.
  - subst.
    inversion H0. subst.
    Fail injection H1. (* TODO: Why does injection fail? *)
 Admitted. (* TODO *)

Definition P_eval x y1 :=
  forall y2,
    x ==> y2 ->
    y1 = y2.

Definition P_eval_bindings_non_rec x y1 :=
  forall y2,
    eval_bindings_nonrec x y1 ->
    eval_bindings_nonrec x y2 ->
    y1 = y2.

Theorem eval__deterministic : forall x y1,
  x ==> y1 ->
  P_eval x y1.
Proof.
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_non_rec).
  - (* E_Let *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    apply H0.
    + assumption.
    + assumption.
  - (* E_LetRec *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
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
  - (* E_ApplyBuiltin3 *)
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
      apply eval_defaultfun__deterministic with (Apply v3 v4).
      * assumption.
      * assumption.
  - (* E_TyInstBuiltin1 *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_TyInstBuiltin1 *)
      reflexivity.
    + (* E_TyInst *)  
      subst.
      assert (Builtin IfThenElse = TyAbs X K y2). {
        apply H0. assumption.
      }
      inversion H2.
  - (* E_TyInst *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_TyInstBuiltin1 *)
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
    intros. unfold P_eval_bindings_non_rec. intros.
    inversion H1. subst.
    inversion H2. subst.
    apply H0. assumption.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_non_rec. intros.
    inversion H6. subst.
    assert (vb = vb0). {
      apply H0. assumption.
    }
    subst.
    assert (t' = t'0). {
      apply substitute__deterministic in H2.
      apply H2 in H16.
      assumption.
    }
    subst.
    assert (bs' = bs'0). {
      apply substitute__deterministic in H1.
      apply H1 in H15.
      assumption.
    }
    subst.
    apply H4.
    + assumption.
    + assumption.
Qed.