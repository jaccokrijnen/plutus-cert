Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Smallstep.

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
Qed.

