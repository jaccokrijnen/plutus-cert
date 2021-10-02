Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.Deterministic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Smallstep.

(*
Lemma multistep_congr_Let : forall bs t t',
    multistepBNR (Let NonRec bs t) t' ->
    Let NonRec bs t -->* t'.
Proof. intros.
  induction H. subst.
  - apply multi_refl.
  - inversion H; subst.
    + eauto with smallstep_db.
    + eauto with smallstep_db.
    + eauto with smallstep_db.
    + eauto with smallstep_db.
Qed.

Lemma multistep_congr_TyAbs : forall X K t t',
    t -->* t' ->
    TyAbs X K t -->* TyAbs X K t'.
Proof. intros. induction H; eauto with smallstep_db. Qed.

Lemma multistep_congr_Apply1 : forall t1 t1' t2,
    t1 -->* t1' ->
    Apply t1 t2 -->* Apply t1' t2.
Proof. intros. induction H; eauto with smallstep_db. Qed.

Lemma multistep_congr_Apply2 : forall v1 t2 t2',
    value v1 ->
    t2 -->* t2' ->
    Apply v1 t2 -->* Apply v1 t2'.
Proof. intros. induction H0; eauto with smallstep_db. Qed.

Lemma multistep_congr_TyInst1 : forall t1 t1' T,
    t1 -->* t1' ->
    TyInst t1 T -->* TyInst t1' T.
Proof. intros. induction H; eauto with smallstep_db. Qed.

Lemma multistep_congr_IWrap : forall F T t0 t0',
    t0 -->* t0' ->
    IWrap F T t0 -->* IWrap F T t0'.
Proof. intros. induction H; eauto with smallstep_db. Qed.

Lemma multistep_congr_Unwrap : forall t0 t0',
    t0 -->* t0' ->
    Unwrap t0 -->* Unwrap t0'.
Proof. intros. induction H; eauto with smallstep_db. Qed.


Lemma multistepBNR_congr_NilB : forall t t',
    t -->* t' ->
    multistepBNR (Let NonRec nil t) (Let NonRec nil t').
Proof. intros. induction H; eauto with smallstep_db. Qed.

Lemma multistepBNR_congr_ConsB1 : forall s x T tb bs t tb',
    tb -->* tb' ->
    multistepBNR (Let NonRec (TermBind s (VarDecl x T) tb  :: bs) t) (Let NonRec (TermBind s (VarDecl x T) tb' :: bs) t).
Proof. intros. induction H; eauto with smallstep_db. Qed.



Definition P_eval t v :=
  value v ->
  t -->* v.

Definition P_eval_bindings_non_rec t v :=
  value v ->
  multistepBNR t v.

Theorem equiv_eval_multistep : forall x y1,
    x ==> y1 ->
    P_eval x y1.
Proof.
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_non_rec).
  - (* E_Let *)
    intros. unfold P_eval. intros.
    apply multi_trans with v. {
      apply multistep_congr_Let.
      apply H0.
      assumption.
    }
    apply multi_refl.
  - (* E_LetRec *)
    intros. unfold P_eval. intros.
    apply multi_refl.
  - (* E_TyAbs *)
    intros. unfold P_eval. intros.
    apply multistep_congr_TyAbs.
    apply H0. 
    inversion H1.
    + subst. assumption.
    + subst. inversion H2. 
  - (* E_LamAbs *)
    intros. unfold P_eval. intros.
    apply multi_refl.
  - (* E_Apply *)
    intros. unfold P_eval. intros.
    apply multi_trans with (Apply (LamAbs x T t0) t2). {
      apply multistep_congr_Apply1.
      apply H0.
      apply V_LamAbs.
    }
    apply multi_trans with (Apply (LamAbs x T t0) v2). {
      apply multistep_congr_Apply2.
      + apply V_LamAbs.
      + apply H2.
        eapply eval_to_value.
        eassumption.
    }
    apply multi_step with t0'. {
      apply ST_ApplyLamAbs.
      + eapply eval_to_value.
        eassumption.
      + assumption.
    }
    apply H5.
    assumption.
  - (* E_Constant *)
    intros. unfold P_eval. intros.
    apply multi_refl.
  - (* E_Builtin *)
    intros. unfold P_eval. intros.
    apply multi_refl.
  - (* E_ApplyBuiltin1 *)
    intros. unfold P_eval. intros.
    apply multi_trans with (Apply v1 t2). {
      apply multistep_congr_Apply1.
      apply H0.
      apply V_Builtin.
      assumption.
    }
    apply multi_trans with (Apply v1 v2). {
      apply multistep_congr_Apply2.
      + apply V_Builtin.
        assumption.
      + apply H3.
        eapply eval_to_value.
        eassumption.
    }
    apply multi_refl.
  - (* E_ApplyBuiltin2 *)
    intros. unfold P_eval. intros.
    apply multi_trans with (Apply v1 t2). {
      apply multistep_congr_Apply1.
      apply H0.
      apply V_Builtin.
      assumption.
    }
    apply multi_trans with (Apply v1 v2). {
      apply multistep_congr_Apply2.
      + apply V_Builtin.
        assumption.
      + apply H3.
        eapply eval_to_value.
        eassumption.
    }
    eapply multi_step. {
      apply ST_ApplyBuiltin2.
      + assumption.
      + eapply eval_to_value.
        eassumption.
      + assumption.
      + eassumption.
    }
    apply multi_refl.
  - (* E_TyInstBuiltin1 *)
    intros. unfold P_eval. intros.
    apply multistep_congr_TyInst1.
    apply H0.
    apply V_Builtin.
    apply V_Builtin0.
    apply le_S. apply le_S. apply le_S. apply le_n.
  - (* E_TyInstTyAbs *)
    intros. unfold P_eval. intros.
    apply multi_trans with (TyInst (TyAbs X K v0) T2). {
      apply multistep_congr_TyInst1.
      apply H0.
      apply V_TyAbs.
      assumption.
    }
    apply multi_step with v0. {
      apply ST_TyInstTyAbs.
    }
    apply multi_refl.
  - (* E_Error *)
    intros. unfold P_eval. intros.
    apply multi_refl.
  - (* E_IWrap *)
    intros. unfold P_eval. intros.
    apply multistep_congr_IWrap.
    apply H0.
    inversion H1. 
    + subst. inversion H2.
    + subst. assumption.
  - (* E_Unwrap *)
    intros. unfold P_eval. intros.
    apply multi_trans with (Unwrap (IWrap F T v0)). {
      apply multistep_congr_Unwrap.
      apply H0.
      apply V_IWrap.
      assumption.
    }
    apply multi_step with v0.
    apply ST_UnwrapWrap.
    apply multi_refl.

  - (* E_NilB_NonRec *)
    intros. unfold P_eval_bindings_non_rec. intros.
    apply multi_trans with (Let NonRec nil v). {
      apply multistepBNR_congr_NilB.
      apply H0.
      assumption.
    }
    apply multi_step with v. {
      apply ST_NilB_NonRec2.
      assumption.
    }
    apply multi_refl.
  - (* E_ConsB_NonRec *)
    intros. unfold P_eval_bindings_non_rec. intros.
    apply multi_trans with (Let NonRec (TermBind s (VarDecl x T) vb :: bs) t). {
      apply multistepBNR_congr_ConsB1.
      apply H0.
      eapply eval_to_value.
      eassumption.
    }
    apply multi_step with (Let NonRec bs' t'). {
      apply ST_ConsB_NonRec2.
      + eapply eval_to_value.
        eassumption.
      + assumption.
      + assumption.
    }
    apply multi_trans with v. {
      apply H4.
      assumption.
    }
    apply multi_refl.
Qed.*)

Lemma compute_defaultfun__LamAbs : forall t x T t0,
  compute_defaultfun t <> Datatypes.Some (LamAbs x T t0).
Proof.
  intros.
  intros Hcon.
  destruct t.
  all: inversion Hcon.
  destruct t1; try discriminate.
  - destruct t1_1; try discriminate.
    + destruct t1_1_1; try discriminate.
      destruct d; try discriminate.
      destruct t1_1_2; try discriminate.
      destruct s; try discriminate.
      destruct u; try discriminate.
      destruct v; try discriminate.
      destruct t1_2; try discriminate.
      destruct s; try discriminate.
      destruct u0; try discriminate.
      destruct v; try discriminate.
      destruct t2; try discriminate.
      destruct s; try discriminate.
      destruct u1; try discriminate.
      destruct v; try discriminate.
    + destruct d; try discriminate.
      all: try solve [
        destruct t1_2; try discriminate;
        destruct s; try discriminate;
        destruct u; try discriminate;
        destruct v; try discriminate;
        destruct t2; try discriminate;
        destruct s; try discriminate;
        destruct u0; try discriminate;
        destruct v; try discriminate
      ].
  - destruct d; try discriminate.
    all: try solve [
      destruct t2; try discriminate;
      destruct s; try discriminate;
      destruct u; try discriminate;
      destruct v; try discriminate
    ].
Qed.

Lemma compute_defaultfun__IfThenElse0 : forall t T0,
  compute_defaultfun t <> Datatypes.Some (TyInst (Builtin IfThenElse) T0).
Proof.
  intros.
  intros Hcon.
  destruct t.
  all: inversion Hcon.
  destruct t1; try discriminate.
  - destruct t1_1; try discriminate.
    + destruct t1_1_1; try discriminate.
      destruct d; try discriminate.
      destruct t1_1_2; try discriminate.
      destruct s; try discriminate.
      destruct u; try discriminate.
      destruct v; try discriminate.
      destruct t1_2; try discriminate.
      destruct s; try discriminate.
      destruct u0; try discriminate.
      destruct v; try discriminate.
      destruct t2; try discriminate.
      destruct s; try discriminate.
      destruct u1; try discriminate.
      destruct v; try discriminate.
    + destruct d; try discriminate.
      all: try solve [
        destruct t1_2; try discriminate;
        destruct s; try discriminate;
        destruct u; try discriminate;
        destruct v; try discriminate;
        destruct t2; try discriminate;
        destruct s; try discriminate;
        destruct u0; try discriminate;
        destruct v; try discriminate
      ].
  - destruct d; try discriminate.
    all: try solve [
      destruct t2; try discriminate;
      destruct s; try discriminate;
      destruct u; try discriminate;
      destruct v; try discriminate
    ].
Qed.

Lemma compute_defaultfun__IfThenElse1 : forall t T0 cond,
  compute_defaultfun t <> Datatypes.Some (Apply (TyInst (Builtin IfThenElse) T0) cond).
Proof.
  intros.
  intros Hcon.
  destruct t.
  all: inversion Hcon.
  destruct t1; try discriminate.
  - destruct t1_1; try discriminate.
    + destruct t1_1_1; try discriminate.
      destruct d; try discriminate.
      destruct t1_1_2; try discriminate.
      destruct s; try discriminate.
      destruct u; try discriminate.
      destruct v; try discriminate.
      destruct t1_2; try discriminate.
      destruct s; try discriminate.
      destruct u0; try discriminate.
      destruct v; try discriminate.
      destruct t2; try discriminate.
      destruct s; try discriminate.
      destruct u1; try discriminate.
      destruct v; try discriminate.
    + destruct d; try discriminate.
      all: try solve [
        destruct t1_2; try discriminate;
        destruct s; try discriminate;
        destruct u; try discriminate;
        destruct v; try discriminate;
        destruct t2; try discriminate;
        destruct s; try discriminate;
        destruct u0; try discriminate;
        destruct v; try discriminate
      ].
  - destruct d; try discriminate.
    all: try solve [
      destruct t2; try discriminate;
      destruct s; try discriminate;
      destruct u; try discriminate;
      destruct v; try discriminate
    ].
Qed.

Lemma compute_defaultfun__IfThenElse2 : forall t T0 cond t_t,
  compute_defaultfun t <> Datatypes.Some (Apply (Apply (TyInst (Builtin IfThenElse) T0) cond) t_t).
Proof.
  intros.
  intros Hcon.
  destruct t.
  all: inversion Hcon.
  destruct t1; try discriminate.
  - destruct t1_1; try discriminate.
    + destruct t1_1_1; try discriminate.
      destruct d; try discriminate.
      destruct t1_1_2; try discriminate.
      destruct s; try discriminate.
      destruct u; try discriminate.
      destruct v; try discriminate.
      destruct t1_2; try discriminate.
      destruct s; try discriminate.
      destruct u0; try discriminate.
      destruct v; try discriminate.
      destruct t2; try discriminate.
      destruct s; try discriminate.
      destruct u1; try discriminate.
      destruct v; try discriminate.
    + destruct d; try discriminate.
      all: try solve [
        destruct t1_2; try discriminate;
        destruct s; try discriminate;
        destruct u; try discriminate;
        destruct v; try discriminate;
        destruct t2; try discriminate;
        destruct s; try discriminate;
        destruct u0; try discriminate;
        destruct v; try discriminate
      ].
  - destruct d; try discriminate.
    all: try solve [
      destruct t2; try discriminate;
      destruct s; try discriminate;
      destruct u; try discriminate;
      destruct v; try discriminate
    ].
Qed.

Lemma eval_builtin_LamAbs : forall v j x T t0,
    value_builtin v ->
    ~ v =[j]=> LamAbs x T t0.
Proof. intros.
  inversion H; subst.
  - intros Hcon.
    inversion Hcon.
  - intros Hcon.
    inversion Hcon; subst.
    all : inversion H4; subst.
    apply compute_defaultfun__LamAbs in H10.
    assumption.
  - intros Hcon.
    inversion Hcon; subst.
    + inversion H5; subst.
      all: inversion H8; subst.
      apply compute_defaultfun__LamAbs in H15.
      assumption.
    + apply compute_defaultfun__LamAbs in H11.
      assumption.
    + inversion H5; subst.
      all: try solve [inversion H6].
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11. 
    + inversion H5; subst.
      all: try solve [inversion H6].
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11.
Qed.

Lemma eval_builtin_IfThenElse1 : forall v j T cond,
    value_builtin v ->
    ~ v =[j]=> Apply (TyInst (Builtin IfThenElse) T) cond.
Proof.
  intros.
  intros Hcon.
  inversion H; subst.
  - inversion Hcon.
  - inversion Hcon; subst.
    all: try solve [inversion H4].
    all: try solve [inversion H7].
    apply compute_defaultfun__IfThenElse1 in H10.
    assumption.
  - inversion Hcon; subst.
    + inversion H5; subst.
      all: try inversion H8; subst.
      apply compute_defaultfun__LamAbs in H15.
      assumption.
    + inversion H8.
    + apply compute_defaultfun__IfThenElse1 in H11.
      assumption.
    + inversion H8; subst.
      all: try inversion H5; subst.
      apply compute_defaultfun__IfThenElse0 in H13.
      assumption.
    + inversion H5; subst.
      all: try inversion H6; subst.
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11.
    + inversion H5; subst.
      all: try inversion H6.
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11.
Qed.

Lemma eval_builtin_IfThenElse2 : forall v j T cond t_t,
    value_builtin v ->
    ~ v =[j]=> Apply (Apply (TyInst (Builtin IfThenElse) T) cond) t_t.
Proof.
  intros.
  intros Hcon.
  inversion H; subst.
  - inversion Hcon.
  - inversion Hcon; subst.
    all: try solve [inversion H4].
    all: try solve [inversion H7].
    * apply compute_defaultfun__IfThenElse2 in H10.
      assumption.
    * inversion H8.
  - inversion Hcon; subst.
    + inversion H5; subst.
      all: try inversion H8; subst.
      apply compute_defaultfun__LamAbs in H15.
      assumption.
    + inversion H8.
    + apply compute_defaultfun__IfThenElse2 in H11.
      assumption.
    + inversion H9; subst.
      all: try inversion H5; subst.
      * inversion H12.
      * apply compute_defaultfun__IfThenElse1 in H12.
        assumption.
      * inversion H8.
    + inversion H5; subst.
      all: try inversion H6; subst.
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11.
    + inversion H5; subst.
      all: try inversion H6.
      * inversion H13.
      * apply compute_defaultfun__IfThenElse2 in H13.
        assumption.
      * inversion H11.
Qed.


Lemma eval_IfThenElse2_LamAbs : forall T cond t_t x T0 t0 j,
    ~ Apply (Apply (TyInst (Builtin IfThenElse) T) cond) t_t =[j]=> LamAbs x T0 t0.
Proof. Admitted.


Definition P_step t t' :=
  forall j v,
    t' =[j]=> v ->
    t =[S j]=> v.

Axiom skip : forall P, P.

Theorem step__eval : forall t t' j v,
    t --> t' ->
    t' =[j]=> v ->
    t =[S j]=> v.
Proof.
  intros t t' j v Hstep.
  generalize dependent v.
  generalize dependent j.
  induction Hstep.
  - (* ST_Let_NilB *) 
    intros. 
    destruct recty.
    + (* recty = NonRec *)
      apply E_Let.
      eapply E_NilB_NonRec.
      assumption.
    + (* recty = Rec *)
      apply E_LetRec.
      eapply E_NilB_Rec.
      assumption.
  - (* ST_LetNonRec_ConsB1 *)
    intros.
    inversion H. subst.
    inversion H4. subst. 
    eapply E_Let.
    rewrite <- plus_Sn_m.
    rewrite <- plus_Sn_m.
    eapply E_ConsB_NonRec.
    all: eauto.
  - (* ST_LetNonRec_ConsB2 *)
    intros.
    inversion H1. subst.
    eapply E_Let.
    replace (S j) with (0 + 1 + j) by reflexivity.
    eapply E_ConsB_NonRec.
    all: eauto.
    eapply eval_value.
    assumption.
  - (* ST_Apply1 *)
    intros.
    inversion H; subst.
    + rewrite <- plus_Sn_m.
      rewrite <- plus_Sn_m.
      rewrite <- plus_Sn_m.
      eapply E_Apply.
      all: eauto.
    + rewrite <- plus_Sn_m.
      eapply E_ApplyBuiltin1.
      all: eauto.
    + rewrite <- plus_Sn_m.
      rewrite <- plus_Sn_m.
      eapply E_ApplyBuiltin2.
      all: eauto.
    + rewrite <- plus_Sn_m.
      eapply E_IfCondition.
      all: eauto.
    + eapply E_IfThenBranch.
      all: eauto.
    + rewrite <- plus_Sn_m. 
      eapply E_IfTrue.
      all: eauto.
    + rewrite <- plus_Sn_m.
      eapply E_IfFalse.
      all: eauto.
  - (* ST_Apply2 *)
    intros.
    inversion H; subst.
    + inversion H2. subst.
      rewrite <- plus_Sn_m.
      rewrite <- plus_Sn_m.
      rewrite plus_n_Sm.
      eapply E_Apply.
      all: eauto.
    + inversion H2. subst.
      inversion H3.
    + inversion H2. subst.
      inversion H3.
    + inversion H2.
    + inversion H4.
    + inversion H2.
    + inversion H2.
  - (* ST_ApplyLamAbs *)
    intros.
    replace (S j) with (0 + 0 + 1 + j) by reflexivity.
    eapply E_Apply.
    all: eauto.
    + econstructor.
    + apply eval_value.
      assumption.
  - (* ST_Apply3 *)
    intros.
    inversion H0; subst.
    + apply eval_builtin_LamAbs in H3; auto.
      destruct H3.
    + rewrite plus_n_Sm.
      eapply E_ApplyBuiltin1.
      all: eauto.
    + rewrite <- plus_Sn_m.
      rewrite plus_n_Sm.
      eapply E_ApplyBuiltin2.
      all: eauto.
    + rewrite plus_n_Sm.
      eapply E_IfCondition.
      all: eauto.
    + apply eval_builtin_IfThenElse1 in H5; auto.
      destruct H5.
    + apply eval_builtin_IfThenElse2 in H3; auto. 
      destruct H3.
    + apply eval_builtin_IfThenElse2 in H3; auto.
      destruct H3.
  - (* ST_ApplyBuiltin *)
    intros.
    apply compute_defaultfun__to_value in H2 as H4.
    apply eval_value in H4.
    unfold P_value in H4.
    assert (v = v0 /\ j = 0) by (eapply eval__deterministic; eauto).
    destruct H5. subst.
    replace 1 with (0 + 0 + 1) by reflexivity.
    eapply E_ApplyBuiltin2.
    all: eauto.
    + apply eval_value.
      apply V_Builtin.
      assumption.
    + apply eval_value.
      assumption.
  - (* ST_ApplyIf *)
    intros.
    inversion H; subst.
    + apply eval_IfThenElse2_LamAbs in H2.
      destruct H2.
    + apply skip.
    + apply skip.
    + apply skip.
    + apply skip.
    + apply skip.
    + apply skip.
  - (* ST_IfTrue *)