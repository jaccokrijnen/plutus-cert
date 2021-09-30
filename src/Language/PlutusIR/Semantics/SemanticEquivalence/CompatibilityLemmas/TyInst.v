Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.


Lemma msubst_TyInst : forall ss t0 T0 t',
    msubst ss (TyInst t0 T0) t' ->
    exists t0', msubst ss t0 t0' /\ t' = TyInst t0' T0.
Proof.
  induction ss.
  - intros. 
    inversion H. subst.
    exists t0.
    split. 
    + apply msubst_nil.
    + reflexivity. 
  - intros.
    inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    subst.
    edestruct IHss as [t0'' Hms0']; eauto.
    eexists.
    split.
    + eapply msubst_cons.
      * apply H7.
      * apply Hms0'.
    + destruct Hms0'.
      subst.
      reflexivity.
Qed.

Lemma msubstA_TyInst : forall ss t0 T0 t',
    msubstA ss (TyInst t0 T0) t' ->
    exists t0', msubstA ss t0 t0' /\ t' = TyInst t0' (msubstT ss T0).
Proof.
  induction ss.
  - intros. 
    inversion H. subst.
    exists t0.
    split. 
    + apply msubstA_nil.
    + reflexivity. 
  - intros.
    inversion H. subst.
    rename t'0 into t''.
    inversion H2.
    subst.
    edestruct IHss as [t0'' [HmsA__t0'' Heq]]; eauto.
    subst.
    eexists.
    split.
    * eapply msubstA_cons. eauto. eauto.
    * reflexivity. 
Qed.

Lemma inspect_eval__TyInst1 : forall t1 T j v,
    TyInst t1 T =[j]=> v ->
    exists j1 v1, t1 =[j1]=> v1 /\ j1 <= j.
Proof.
  intros.
  inversion H. all: subst.
  - exists j.
    exists (Builtin IfThenElse).
    split; auto.
  - exists k1.
    exists (TyAbs X K t2).
    split; auto.
    assert (forall a b c, a <= a + b + c). {
      intros.
      induction b; induction c.
      - rewrite <- plus_n_O.
        rewrite <- plus_n_O.
        auto.
      - rewrite <- plus_n_O.
        rewrite <- plus_n_O in IHc.
        rewrite <- plus_n_Sm.
        auto.
      - rewrite <- plus_n_O.
        rewrite <- plus_n_O in IHb.
        rewrite <- plus_n_Sm.
        auto.
      - rewrite <- plus_n_Sm.
        rewrite <- plus_n_Sm.
        rewrite plus_Sn_m.
        rewrite <- plus_n_Sm in IHb.
        auto.
    }
    apply H0.
Qed.

(*
Lemma e : forall e,
    RD ck rho ->
    (mupdate ck epty) |-* T : K ->
    Rel RC k T rho () *)

Lemma compatibility_TyInst: forall Delta Gamma e e' bX K T T' S T1,
    Delta |-* T1 : K ->
    substituteTCA bX T1 T T' ->
    normalise T' S ->
    LR_logically_approximate Delta Gamma e e' (Ty_Forall bX K T) ->
    LR_logically_approximate Delta Gamma (TyInst e T1) (TyInst e' T1) S.
Proof.
  intros Delta Gamma e e' bX K T T' S T1 Hkind__T1 Hstca__T' Hnorm IH_LR.
  unfold LR_logically_approximate.
  
  split. {
    eapply T_TyInst.
    - eapply IH_LR.
    - apply Hkind__T1.
    - apply Hstca__T'.
    - apply Hnorm.
  }

  split. {
    eapply T_TyInst.
    - eapply IH_LR.
    - apply Hkind__T1.
    - apply Hstca__T'.
    - apply Hnorm.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  destruct (msubstA_TyInst _ _ _ _ HmsA__e_msa) as [eb_msa [HmsA__eb_msa Heq]].
  destruct (msubstA_TyInst _ _ _ _ HmsA__e'_msa) as [eb'_msa [HmsA__eb'_msa Heq']].
  subst.
  destruct (msubst_TyInst _ _ _ _ Hms__e_ms) as [eb_ms [Hms__eb_ms Heq]].
  destruct (msubst_TyInst _ _ _ _ Hms__e'_ms) as [eb'_ms [Hms__eb'_ms Heq']].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR.
      eapply T_TyInst; eauto.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR. destruct H0.
      eapply T_TyInst; eauto.
    - rewrite mupd_empty; eauto.
  }

  intros j Hlt__j e_f Hev__e_f.

  destruct (inspect_eval__TyInst1 _ _ _ _ Hev__e_f) as [j_1 [e_f1 [Hev__e_f1 Hlt__j_1]]].

  unfold LR_logically_approximate in IH_LR.
  destruct IH_LR as [_ [_ IH]].
  assert (IH_RC : RC k (Ty_Forall bX K T) rho eb_ms eb'_ms) by eauto.
  
  autorewrite with RC in IH_RC. 
  destruct IH_RC as [_ [_ IH_RC]].
  assert (j_1 < k) by eauto using Nat.le_lt_trans.
  remember (IH_RC j_1 H e_f1 Hev__e_f1).
  clear Heqe0. clear IH_RC. rename e0 into IH_RC.
  destruct IH_RC as [e'_f1 [j'_1 [Hev__e'_f1 Hie]]].


  assert (exists t_, e_f1 = TyAbs bX K t_) by apply skip.
  assert (exists t_', e'_f1 = TyAbs bX K t_') by apply skip.
  destruct H0 as [t_ Heq]. subst.
  destruct H1 as [t_' Heq']. subst.

  assert (TyAbs bX K t_ = TyAbs bX K t_) by reflexivity.
  assert (TyAbs bX K t_' = TyAbs bX K t_') by reflexivity.
  assert (Rel (msubstT (msyn1 rho) T1) (msubstT (msyn2 rho) T1) (fun k t1 t2 => RC k T1 rho t1 t2)). {
    unfold Rel.
    intros.
    split. {
      eapply RC_typable_empty_1; eauto.
    }
    split. {
      eapply RC_typable_empty_2; eauto.
    }
    intros.
    eapply RC_monotone; eauto.
  }
  assert (empty |-* (msubstT (msyn1 rho) T1) : K). {
    apply skip.
  }
  assert (empty |-* (msubstT (msyn2 rho) T1) : K). {
    apply skip.
  }

  assert (exists aaa, substituteA bX (msubstT (msyn1 rho) T1) t_ aaa). {
    eapply substituteA_total.
  }
  assert (exists bbb, substituteA bX (msubstT (msyn2 rho) T1) t_' bbb). {
    eapply substituteA_total.
  }
  destruct H5.
  destruct H6.

  remember (Hie _ _ H0 H1 _ _ _ _ _ H3 H4 H2 H5 H6).
  clear Heqr.

  assert (k - j_1 - 1 < k - j_1) by apply skip.
  apply r in H7.

  assert (exists j_2, k = j_1 + 1 + j_2) by apply skip.
  destruct H8 as [j_2 temp].

  assert (j_2 < k - j_1 - 1) by apply skip.
  autorewrite with RC in H7.
  destruct H7 as [_ [_ H7]].
  assert (t_ =[j_2]=> e_f) by apply skip.
  remember (H7 _ H8 _ H9).
  clear Heqe0.
  destruct e0 as [e'_f [j'_2 [Hev__e'_f HHH]]].
  exists e'_f.
  eexists.
  split. {
    eapply E_TyInst; eauto.
    apply skip.
  } 
Admitted.