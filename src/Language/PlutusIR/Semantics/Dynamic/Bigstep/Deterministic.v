Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.


(** * [substitute] is deterministic*)

Definition P_substitute (t t' : Term) : Prop :=
  forall x s t'',
    substitute x s t t'' ->
    t' = t''. 

Definition P_substitute_letrec (t t' : Term) : Prop :=
  forall x s t'',
    substitute_letrec x s t t'' ->
    t' = t''.

Definition P_substitute_binding (b b' : Binding) : Prop :=
  forall x s b'',
    substitute_binding x s b b'' ->
    b' = b''.
    
Theorem substitute__deterministic : forall x s,
    (* P =  *) (forall t t', substitute x s t t' -> (forall t'', substitute x s t t'' -> t' = t'')) /\
    (* P0 = *) (forall t t', substitute_letrec x s t t' -> (forall t'', substitute_letrec x s t t'' -> t' = t'')) /\
    (* P1 = *) (forall b b', substitute_binding x s b b' -> (forall b'', substitute_binding x s b b'' -> b' = b'')).
Proof.
  intros x s.
  apply substitute__mutind.
  - (* S_LetNonRec_Nil1 *)
    intros. 
    inversion H1.
    subst.
    f_equal.
    eapply H0; eauto.
  - (* S_LetNonRec_Cons1 *)
    intros. 
    inversion H2.
    + subst.
      f_equal.
      f_equal.
      eapply H1; eauto.
    + subst.
      exfalso.
      auto.
  - (* S_LetNonRec_Cons2 *)
    intros. 
    inversion H4.
    + subst.
      exfalso.
      auto.
    + subst.
      apply H3 in H11.
      inversion H11. subst.
      f_equal.
      f_equal. 
      auto.
  - (* S_LetRec1 *)
    intros.
    inversion H0. 
    + subst.
      reflexivity.
    + subst.
      exfalso.
      auto.
  - (* S_LetRec2 *)
    intros.
    inversion H2.
    + subst.
      exfalso.
      auto.
    + subst.
      eauto.
  - (* S_Var1 *)
    intros. 
    inversion H. 
    + subst.
      reflexivity.
    + subst.
      assert (x = x) by reflexivity.
      exfalso.
      auto.
  - (* S_Var2 *)
    intros. 
    inversion H0. subst.
    + subst.
      assert (y = y) by reflexivity.
      apply H in H1.
      destruct H1.
    + subst.
      reflexivity.
  - (* S_TyAbs *)
    intros.  
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_LamAbs1 *)
    intros. 
    inversion H.
    + subst.
      reflexivity.
    + subst.
      assert (x = x) by auto.
      exfalso.
      auto.
  - (* S_LamAbs2 *)
    intros. 
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
    intros. 
    inversion H3. subst.
    assert (t1' = t1'0) by auto.
    assert (t2' = t2'0) by auto.
    subst.
    reflexivity.
  - (* S_Constant *)
    intros. 
    inversion H. subst.
    reflexivity.
  - (* S_Builtin *)
    intros. 
    inversion H. subst.
    reflexivity.
  - (* S_TyInst *)
    intros. 
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_Error *)
    intros. 
    inversion H. subst.
    reflexivity.
  - (* S_IWrap *)
    intros. 
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.
  - (* S_Unwrap *)
    intros. 
    inversion H1. subst.
    assert (t0' = t0'0) by auto.
    subst.
    reflexivity.

  - (* S_NilB_Rec *)
    intros.
    inversion H1. subst.
    f_equal.
    auto.
  - (* S_ConsB_Rec *)
    intros.
    inversion H3. subst.
    apply H2 in H9.
    inversion H9. subst.
    f_equal.
    f_equal.
    auto.
  
  - (* S_TermBind *)
    intros. 
    inversion H1. subst.
    assert (t' = t'0) by auto.
    subst.
    reflexivity.
  - (* S_TypeBind *)
    intros.
    inversion H. subst.
    reflexivity.
  - (* S_DatatypeBind *)
    intros.
    inversion H. subst.
    reflexivity.
Qed.

Corollary substitute_term__deterministic : forall x s t t' t'', 
    substitute x s t t' -> 
    substitute x s t t'' -> 
    t' = t''.
Proof. intros. eapply substitute__deterministic in H; eauto. Qed.

Theorem substituteA__deterministic : forall X S t t' t'', 
    substituteA X S t t' ->
    substituteA X S t t'' ->
    t' = t''. 
Proof. Admitted.

(** * [eval] is deterministic *)

(** The next Lemma seems to follow easily from inversion on the assumption and it is 
    therefore not really necessary to dedicate a Lemma to it. However, we need to  prove 
    this Lemma separately because the [inversion] tactic could not figure out this equality 
    during the [eval__deterministic] proof below. *)
Lemma compare_IfThenElse_conditions : forall T T' (t_e t_e' : Term) cond cond', 
    Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))) t_e = 
      Apply (Apply (TyInst (Builtin IfThenElse) T') (Constant (Some (ValueOf DefaultUniBool cond')))) t_e' -> 
    cond = cond'.
Proof.
  intros.
  inversion H. 
  subst.
  apply Eqdep.EqdepTheory.inj_pair2 in H2.
  subst.
  reflexivity.
Qed.

(** ** Predicates *)
Definition P_eval x y1 (k1 : nat) :=
  forall y2 k2,
    x =[k2]=> y2 ->
    y1 = y2 /\ k1 = k2.

Definition P_eval_bindings_nonrec x y1 (k1 : nat) :=
  forall y2 k2,
    eval_bindings_nonrec x y2 k2 ->
    y1 = y2 /\ k1 = k2.

Definition P_eval_bindings_rec bs0 x y1 (k1 : nat) :=
  forall y2 k2,
    eval_bindings_rec bs0 x y2 k2->
    y1 = y2 /\ k1 = k2.

(** ** The main result *)
Theorem eval__deterministic : forall x y1 k1,
  x =[k1]=> y1 ->
  P_eval x y1 k1.
Proof.
  (*
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec).
  - (* E_Let *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    eapply H0.
    eassumption.
  - (* E_LetRec *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    eapply H0.
    eassumption.
  - (* E_TyAbs *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    split; auto.
  - (* E_LamAbs *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    split; auto.
  - (* E_Apply *)
    intros. unfold P_eval. intros.
    inversion H6.
    + (* E_Apply *)
      subst.

      assert (LamAbs x T t0 = LamAbs x0 T0 t5). {
        eapply H0. eassumption.
      }
      inversion H7. subst.
      assert (v2 = v1). {
        eapply H2. eassumption.
      }
      subst.
      assert (t0'0 = t0'). {
        apply substitute__deterministic with x0 v1 t5.
        + assumption.
        + assumption.
      }
      subst. 

      split.
      * eapply H5.
        eassumption.
      * assert (k1 = k4). {
          eapply H0. eassumption.
        }
        assert (k2 = k5). {
          eapply H2. eassumption.
        }
        assert (k0 = k6). {
          eapply H5. eassumption.
        } 
        subst.
        reflexivity.
    + (* E_ApplyBuiltin1 *)
      subst.
      assert (LamAbs x T t0 = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H14.
    + (* E_ApplyBuiltin2 *) 
      subst. 
      assert (LamAbs x T t0 = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H10.
    + (* E_IfCondition*)
      subst.
      assert (LamAbs x T t0 = TyInst (Builtin IfThenElse) T0). {
        eapply H0. eassumption.
      }
      inversion H7.
    + (* E_IfThenBranch *)
      subst.
      assert (LamAbs x T t0 = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      inversion H7.
    + (* E_IfTrue *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        eapply H0. eassumption.
      }
      inversion H7.
    + (* E_IfFalse *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        eapply H0. eassumption.
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
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
    + (* E_AppltBuiltin1 *)
      subst.
      assert (v1 = v0). {
        eapply H0. eassumption.
      }
      subst.
      assert (v2 = v3). {
        eapply H3. eassumption.
      }
      subst.
      reflexivity.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (v1 = v0). {
        eapply H0. eassumption.
      }
      subst.
      assert (v2 = v3). {
        eapply H3. eassumption.
      }
      subst.
      apply H11 in H4.
      destruct H4.
    + (* E_IfCondition*)
      subst.
      assert (v1 = TyInst (Builtin IfThenElse) T). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (v1 = Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
    + (* E_IfFalse *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
  - (* E_ApplyBuiltin2 *)
    intros. unfold P_eval. intros.
    inversion H6. subst.
    + (* E_Apply *) 
      subst.
      assert (v1 = LamAbs x T t4). {
        eapply H0. eassumption.
      }
      subst.
      inversion H1.
    + (* E_ApplyBuiltin1 *)
      subst.
      assert (v1 = v3). {
        eapply H0. eassumption.
      }
      subst.
      assert (v2 = v4). {
        eapply H3. eassumption.
      }
      subst.
      apply H4 in H14.
      destruct H14.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (v1 = v3). {
        eapply H0. eassumption.
      }
      subst.
      assert (v2 = v4). {
        eapply H3. eassumption.
      }
      subst. 
      rewrite H5 in H15. 
      inversion H15. 
      subst. 
      reflexivity.
    + (* E_IfCondition*)
      subst.
      assert (v1 = TyInst (Builtin IfThenElse) T). {
        eapply H0. eassumption.
      }
      subst.
      inversion H1.
    + (* E_IfThenBranch *)
      subst.
      assert (v1 = Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      subst.
      inversion H1.
    + (* E_IfTrue *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        eapply H0. eassumption.
      }
      subst.
      inversion H1.
    + (* E_IfFalse *)
      subst.
      assert (v1 = Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        eapply H0. eassumption.
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
      assert (Builtin IfThenElse = TyAbs X K t2). {
        eapply H0. eassumption.
      }
      inversion H2.
  - (* E_IfCondition *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (TyInst (Builtin IfThenElse) T = LamAbs x T0 t0). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (TyInst (Builtin IfThenElse) T = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H7.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (TyInst (Builtin IfThenElse) T = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      f_equal.
      * eapply H0. eassumption.
      * eapply H2. eassumption.
    + (* E_IfThenBranch *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond0)))). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
    + (* E_IfFalse *)
      subst.
      assert (TyInst (name := Strings.String.string) (binderName := Strings.String.string) (Builtin IfThenElse) T = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        eapply H0. eassumption.
      }
      subst.
      inversion H4.
  - (* E_IfThenBranch *)
    intros. unfold P_eval. intros.
    inversion H1.
    + (* E_Apply *) 
      subst.
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = LamAbs x T0 t0). {
        eapply H0. eassumption.
      }
      inversion H2.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H9.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H5.
    + (* E_IfCondition*)
      subst.
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = (TyInst (Builtin IfThenElse) T0)). {
        eapply H0. eassumption.
      }
      inversion H2.
    + (* E_IfThenBranch *)
      subst.
      f_equal.
      eapply H0. eassumption.
    + (* E_IfTrue *)
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        eapply H0. eassumption.
      }
      subst.
      inversion H8.
    + (* E_IfFalse *)
      subst.
      assert (Apply (name := Strings.String.string) (binderName := Strings.String.string) (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond))) = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        eapply H0. eassumption.
      }
      inversion H2.
  - (* E_IfTrue *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = LamAbs x T0 t0). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H11.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = (TyInst (Builtin IfThenElse) T0)). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        eapply H0. eassumption.
      }
      inversion H4.
      subst.
      eapply H2.
      eassumption.
    + (* E_IfFalse *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool true)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        eapply H0. eassumption.
      }
      apply compare_IfThenElse_conditions in H4.
      discriminate.
  - (* E_IfFalse *)
    intros. unfold P_eval. intros.
    inversion H3.
    + (* E_Apply *) 
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = LamAbs x T0 t0). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_ApplyBuiltin1 *)
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H11.
    + (* E_ApplyBuiltin2 *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = v1). {
        eapply H0. eassumption.
      }
      subst.
      inversion H7.
    + (* E_IfCondition*)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = (TyInst (Builtin IfThenElse) T0)). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_IfThenBranch *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      inversion H4.
    + (* E_IfTrue *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t0). {
        eapply H0. eassumption.
      }
      apply compare_IfThenElse_conditions in H4.
      discriminate.
    + (* E_IfFalse *)
      subst.
      assert (Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool false)))) t_t = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t0). {
        eapply H0. eassumption.
      }
      inversion H4.
      subst.
      eapply H2.
      eassumption.
  - (* E_TyInst *)
    intros. unfold P_eval. intros.
    inversion H4.
    + (* E_IfTyInst *)
      subst.
      assert (TyAbs X K t0 = Builtin IfThenElse). {
        eapply H0. eassumption.
      }
      inversion H5.
    + (* E_TyInst *)
      subst.
      assert (TyAbs X K t0 = TyAbs X0 K0 t3). {
        eapply H0. eassumption.
      }
      inversion H5. subst.
      assert (t0' = t0'0). {
        apply annotsubst__deterministic with X0 T2 t3; auto.
      }
      subst.
      eapply H3.
      eassumption.
  - (* E_Error *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    reflexivity.
  - (* E_IWrap *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    f_equal.
    eapply H0.
    eassumption.
  - (* E_Unwrap *)
    intros. unfold P_eval. intros.
    inversion H1. subst.
    assert (IWrap F T v0 = IWrap F0 T0 y2). {
      eapply H0. eassumption.  
    }
    inversion H2. subst.
    reflexivity.
  
  - (* E_NilB_NonRec  *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H1. subst.
    eapply H0. eassumption.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_nonrec. intros.
    inversion H4. subst.
    assert (vb = vb0). {
      eapply H0. eassumption.
    }
    subst.
    assert (Let NonRec bs' t' = Let NonRec bs'0 t'0). {
      apply substitute__deterministic in H1.
      apply H1 in H14.
      assumption.
    }
    inversion H5. 
    subst.
    eapply H3.
    eassumption.
  
  - (* E_NilB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H1. subst.
    eapply H0.
    eassumption.
  - (* E_ConsB_Rec *)
    intros. unfold P_eval_bindings_rec. intros.
    inversion H2. subst.
    assert (Let Rec bs' t' = Let Rec bs'0 t'0). {
      apply substitute__deterministic in H.
      apply H in H12.
      assumption.
    }
    inversion H3. 
    subst.
    eapply H1.
    eassumption.
Qed.
*)
Admitted.