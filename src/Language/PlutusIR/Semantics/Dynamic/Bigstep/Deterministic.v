Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.

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
Definition P_eval x y1 (j1 : nat) :=
  forall y2 j2,
    x =[j2]=> y2 ->
    y1 = y2 /\ j1 = j2.

Definition P_eval_bindings_nonrec x y1 (j1 : nat) :=
  forall y2 j2,
    eval_bindings_nonrec x y2 j2 ->
    y1 = y2 /\ j1 = j2.

Definition P_eval_bindings_rec bs0 x y1 (j1 : nat) :=
  forall y2 j2,
    eval_bindings_rec bs0 x y2 j2->
    y1 = y2 /\ j1 = j2.

(** ** The main result *)
Theorem eval__deterministic : forall x y1 j1,
  x =[j1]=> y1 ->
  P_eval x y1 j1.
Proof.
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
    inversion H5.
    + (* E_Apply *)
      subst.

      assert (LamAbs x T t0 = LamAbs x0 T0 t5). {
        eapply H0. eassumption.
      }
      inversion H6. subst.
      assert (v2 = v1). {
        eapply H2. eassumption.
      }
      subst.

      split.
      * eapply H4. 
        eassumption.
      * assert (j1 = j4). {
          eapply H0. eassumption.
        }
        assert (j2 = j5). {
          eapply H2. eassumption.
        }
        assert (j0 = j6). {
          eapply H4. eassumption.
        } 
        subst.
        reflexivity.
    + (* E_ApplyExtBuiltin *)
      subst.
      assert (LamAbs x T t0 = ExtBuiltin f args). {
        eapply H0. eassumption.
      }
      inversion H6.
    + (* E_IfCondition*)
      subst.
      assert (LamAbs x T t0 = TyInst (Builtin IfThenElse) T0). {
        eapply H0. eassumption.
      }
      inversion H6.
    + (* E_IfThenBranch *)
      subst.
      assert (LamAbs x T t0 = Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool cond)))). {
        eapply H0. eassumption.
      }
      inversion H6.
    + (* E_IfTrue *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool true)))) t_t). {
        eapply H0. eassumption.
      }
      inversion H6.
    + (* E_IfFalse *)
      subst.
      assert (LamAbs x T t0 = Apply (Apply (TyInst (Builtin IfThenElse) T0) (Constant (Some (ValueOf DefaultUniBool false)))) t_t). {
        eapply H0. eassumption.
      }
      inversion H6.
  - (* E_Constant *)
    intros. unfold P_eval. intros.
    inversion H. subst.
    auto.
  - (* E_Builtin *)
    intros. unfold P_eval. intros.
    inversion H0.
    + subst.
      auto.
    + subst.
      exfalso.
      eauto.
  - (* E_ExtBuiltinPartiallyApplied *)
    intros. unfold P_eval. intros.
    inversion H0. all: subst.
    + auto.
    + rewrite H3 in H.
      apply PeanoNat.Nat.lt_irrefl in H.
      exfalso.
      auto.
  - (* E_ExtBuiltinFullyApplied *)
    intros. unfold P_eval. intros.
    inversion H1. all: subst.
    + rewrite H in H6.
      apply PeanoNat.Nat.lt_irrefl in H6.
      exfalso. auto.
    + rewrite H0 in H7.
      inversion H7. subst. 
      auto.
  - (* E_ApplyExtBuiltin *)
    intros. unfold P_eval. intros.
    inversion H5. subst.
    + (* E_Apply *) 
      subst.
      assert (ExtBuiltin f args = LamAbs x T t4). {
        eapply H0. eassumption.
      }
      inversion H6.
    + (* E_ApplyExtBuiltin *)
      subst.
      assert (ExtBuiltin f args = ExtBuiltin f0 args0 /\ j1 = j4). {
        eapply H0. eassumption.
      }
      destruct H6.
      inversion H6.
      subst.
      assert (v2 = v1 /\ j2 = j5). {
        eapply H2. eassumption.
      }
      destruct H7.
      subst.
      assert (v0 = y2 /\ j3 = j6). {
        eapply H4. assumption.
      }
      destruct H7. subst.
      auto.
(*
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
      assert (Builtin IfThenElse = TyAbs X j t2). {
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
      assert (TyAbs X j t0 = Builtin IfThenElse). {
        eapply H0. eassumption.
      }
      inversion H5.
    + (* E_TyInst *)
      subst.
      assert (TyAbs X j t0 = TyAbs X0 j0 t3). {
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