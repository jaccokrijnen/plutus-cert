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
Admitted. (* TODO *)

(** * [eval] is deterministic *)

Theorem eval_defaultfun__deterministic : forall t v1 v2,
  eval_defaultfun t v1 ->
  eval_defaultfun t v2 ->
  v1 = v2.
Proof. Admitted. (* TODO *)

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