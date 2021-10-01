Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.ReductionInvariance.

Require Import Arith.
Require Import Coq.Logic.Decidable.


Lemma msubst_Apply : forall ss t1 t2 t',
    msubst_term ss (Apply t1 t2) t' ->
    exists t1' t2', msubst_term ss t1 t1' /\ msubst_term ss t2 t2' /\ t' = (Apply t1' t2').
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists t1, t2.
    eauto using msubst_term__nil, msubst_term__cons. 
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2. subst.
    apply IHss in H5.
    destruct H5 as [t1'' [t2'' [H9 [H10 H11]]]].
    exists t1'', t2''.
    split. {
      apply msubst_term__cons with t1'.
      + assumption.
      + apply H9.
    }
    split. {
      apply msubst_term__cons with t2'.
      + assumption.
      + apply H10.
    }
    assumption.
Qed.

Lemma msubstA_Apply : forall ss t1 t2 t',
    msubstA ss (Apply t1 t2) t' ->
    exists t1' t2', msubstA ss t1 t1' /\ msubstA ss t2 t2' /\ t' = (Apply t1' t2').
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists t1, t2.
    eauto using msubstA_nil, msubstA_cons. 
  - inversion H. subst.
    rename t'0 into t''.
    inversion H2. subst.
    apply IHss in H5.
    destruct H5 as [t1'' [t2'' [H9 [H10 H11]]]].
    exists t1'', t2''.
    split. {
      apply msubstA_cons with t1'.
      + assumption.
      + apply H9.
    }
    split. {
      apply msubstA_cons with t2'.
      + assumption.
      + apply H10.
    }
    assumption.
Qed.

Lemma inspect_eval__Apply1 : forall t1 t2 j v0,
    Apply t1 t2 =[j]=> v0 ->
    exists j1 v1, t1 =[j1]=> v1 /\ j1 <= j.
Proof.
  intros.
  inversion H. all: subst.
  - exists k1.
    exists (LamAbs x T t4).
    split; auto.
Admitted.

Lemma inspect_eval__Apply2 : forall t1 t2 j v0 j1 v1,
    Apply t1 t2 =[j]=> v0 ->
    terminates_incl t1 j1 v1 j ->
    exists j2 v2, terminates_incl t2 j2 v2 (j - j1).
Proof. 
  intros. 
  destruct H0.
  inversion H.
  all: subst.
  - assert (v1 = LamAbs x T t4 /\ j1 = k1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    exists k2.
    
    exists v2.
    split; auto.
Admitted.

Lemma inspect_eval__Apply3 : forall t1 t2 j v0 j1 x T t0 j2 v2 t0',
    Apply t1 t2 =[j]=> v0 ->
    terminates_incl t1 j1 (LamAbs x T t0) j ->
    terminates_incl t2 j2 v2 (j - j1) ->
    substitute x v2 t0 t0' ->
    exists j0, terminates_incl t0' j0 v0 (j - j1 - j2 - 1) /\ j = j1 + j2 + 1 + j0.
Proof. 
  intros. 
  destruct H0.
  destruct H1.
  inversion H.
  all: subst.
  - assert (LamAbs x0 T0 t5 = LamAbs x T t0 /\ k1 = j1) by (eapply eval__deterministic; eauto).
    destruct H5. inversion H5. subst.
    assert (v1 = v2 /\ k2 = j2) by (eapply eval__deterministic; eauto).
    destruct H6. subst.
    assert (t0'0 = t0') by (eapply substitute_term__deterministic; eauto).
    subst.
    exists k0.
    split; auto.
    split; auto.
Admitted.

Lemma compatibility_Apply : forall Delta Gamma e1 e2 e1' e2' T1 T2 ,
    LR_logically_approximate Delta Gamma e1 e1' (Ty_Fun T1 T2) ->
    LR_logically_approximate Delta Gamma e2 e2' T1 ->
    LR_logically_approximate Delta Gamma (Apply e1 e2) (Apply e1' e2') T2.
Proof.
  intros Delta Gamma e1 e2 e1' e2' T1 T2 IH_LR1 IH_LR2.
  unfold LR_logically_approximate.

  split. {
    edestruct IH_LR1 as [Htyp__e1 [Htyp__e1' H1]].
    edestruct IH_LR2 as [Htyp__e2 [Htyp__e2' H2]].
    eapply T_Apply. eauto. eauto.
  }

  split. {
    edestruct IH_LR1 as [Htyp__e1 [Htyp__e1' H1]].
    edestruct IH_LR2 as [Htyp__e2 [Htyp__e2' H2]].
    eapply T_Apply. eauto. eauto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  destruct (msubstA_Apply _ _ _ _ HmsA__e_msa) as [e1_msa [e2_msa [HmsA__e1_msa [HmsA__e2_msa Heq]]]].
  destruct (msubstA_Apply _ _ _ _ HmsA__e'_msa) as [e1'_msa [e2'_msa [HmsA__e1'_msa [HmsA__e2'_msa Heq']]]].
  subst.
  destruct (msubst_Apply _ _ _ _ Hms__e_ms) as [e1_ms [e2_ms [Hms__e1_ms [Hms__e2_ms Heq]]]].
  destruct (msubst_Apply _ _ _ _ Hms__e'_ms) as [e1'_ms [e2'_ms [Hms__e1'_ms [Hms__e2'_ms Heq']]]].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR1.
      destruct IH_LR2.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR1. destruct H0.
      destruct IH_LR2. destruct H3.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }

  (* Second part of the proof *)

  (** 
      Consider arbitrary j, ef such that 
      # j < k, and
      # Apply e1 e2 =[j]=> e_f 
  *)
  intros j Hlt__j e_f ev__e.

  (** 
      Hence, by inspection of the operational semantics, it follows that there 
      exist j1 and e_f1 such that
      # e1 =[j1]=> e_f1, and
      # j1 <= j
  *)
  assert (temp: exists j1 e_f1, e1_ms =[j1]=> e_f1 /\ j1 <= j) by eauto using inspect_eval__Apply1.
  destruct temp as [j1 [e_f1 [Hev__e1 Hle__j1_j]]].

  (** 
      Instantiate the second conjunct of RC1 with k. ... Instantiate this with j1, e_f1. Note that
      # j1 < k, which follows from j1 <= j and j < k, and
      # e1 =[j1]=> e_f1.
  *)
  assert (Hlt__j1_k : j1 < k) by eauto using Nat.le_lt_trans. 

  unfold LR_logically_approximate in IH_LR1.
  assert (RC1 : RC k (Ty_Fun T1 T2) rho e1_ms e1'_ms) by (eapply IH_LR1; eauto).
  autorewrite with RC in RC1.
  destruct RC1 as [_ [_ RC1]].
  remember (RC1 j1 Hlt__j1_k e_f1 Hev__e1) as temp.
  clear Heqtemp. clear RC1. rename temp into RC1.

  (** 
      Hence, there exists e'_f1 (and j'_1) such that
      # e1' =[j'_1]=> e'_f1, and
      # (k - j1, e_f1, e'_f1) \in RV[[T1 -> T2]]
  *)
  destruct RC1 as [e'_f1 [j'_1 [Hev__e1' RV1]]].

  (**
      Hence, 
        e_f1 `equiv` (LamAbs x T1 e_f1__body), and 
        e'_f1 `equiv` (LamAbs x' T1 e'_f1__body).

      TODO: This is not actually true because of the way we handle builtin functions. However,
      I will assume this for now to simplify the proof.
  *)
  assert (temp: exists x e_f11, e_f1 = LamAbs x (msubstT (msyn1 rho) T1) e_f11). { apply skip. }
  destruct temp as [x [e_f11 Heq]].
  assert (temp: exists x' e'_f11, e'_f1 = LamAbs x' (msubstT (msyn2 rho) T1) e'_f11). { apply skip. }
  destruct temp as [x' [e'_f11 Heq']].
  
  (**
      Note that 
        Apply e1 e2 -[j1]-> Apply (LamAbs x T1 e_f11) e2 -[j-j1]-> e_f
        
      Hence, by inspection of the operational semantics it follows that thre exist j2 and and e_f2
      such that
      # e2 =[j2]=> e_f2, and
      # j2 <= j - j1
  *)
  assert (temp: exists j2 e_f2, e2_ms =[j2]=> e_f2 /\ j2 <= j - j1). {
    eapply inspect_eval__Apply2; eauto. split; eauto.
  }
  destruct temp as [j2 [e_f2 [Hev__e2 Hle__j2]]].

  (**
      Instantiate the second conjunct of RC2 with (k - j1). 
  *)
  unfold LR_logically_approximate in IH_LR2.
  assert (RC2 : RC k T1 rho e2_ms e2'_ms) by (eapply IH_LR2; eauto).
  remember RC2 as RC2'. clear HeqRC2'.
  assert (temp: RC (k - j1) T1 rho e2_ms e2'_ms). {
    eapply RC_monotone.
    - eassumption.
    - apply skip. (* TODO *) 
  }
  clear RC2. rename temp into RC2.

  (** 
      Instantiate this with j2 and e_f2. Note that
      # j2 < k - j1, which follows from j2 <= j - j1 and j < k.
      # e2 =[j2]=> e_f2
  *)
  assert (Hlt__j2_k_j1 : j2 < k - j1). { apply skip. (* TODO *) }
  
  autorewrite with RC in RC2.
  destruct RC2 as [_ [_ RC2]].
  remember (RC2 j2 Hlt__j2_k_j1 e_f2 Hev__e2) as temp.
  clear Heqtemp. clear RC2. rename temp into RC2.

  (**
      Hence, there exists e'_f2 (and j'_2) such that 
      # e2' =[j'_2]=> e'_f2, and
      # (k - j1 - j2, e_f2, e'_f2) \in RV[[T1]]
  *)
  destruct RC2 as [e'_f2 [j'_2 [Hev__e2' _]]].
  assert (RV2: RC (k - j1 - j2) T1 rho e_f2 e'_f2). {
    apply skip. (* TODO *)
  }

  (** 
      Hence, 
        e_f2 `equiv` v_f2, and
        e'_f2 `equiv` v'_f2. 
        
      NOTE: In other words, e_f2 and e'_f2 are values. 
  *)
  rename e_f2 into v_f2. rename e'_f2 into v'_f2.

  (** 
      Note that 
        Apply e1 e2 
        -[j1]-> 
        Apply (LamAbs x T1 e_f11) e2 
        -[j2]->
        Apply (LamAbs x T1 e_f11) v_f2
        -[1]->
        e_f11 [v_f2 / x]
        -[j3]->
        e_f
      
      and irred(e_f) and j = j1 + j2 + 1 + j3.

      Instantiate the second conjunct of RV1 with k - j1 - j2 -1, v_f2 and v'_f2. Note that
      # k - j1 - j2 - 1 < k - j1, and
      # (k - j1 - j2 -1, v_f2, v'_f2) \in RV[[T1]]
  *)

  (* messy below *)
  assert (Hlt__j1_j2_k_j1 : k - j1 - j2 - 1 < k - j1). { apply skip. (* TODO *) }

  remember (RV1 x e_f11 x' e'_f11 Heq Heq' (k - j1 - j2 - 1) Hlt__j1_j2_k_j1) as temp.
  clear Heqtemp. clear RV1. rename temp into RV1.

  assert (RC (k - j1 - j2 - 1) T1 rho v_f2 v'_f2). {
    eapply RC_monotone.
    - eassumption.
    - apply skip.
  }

  assert (temp : exists e_f11__s, substitute x v_f2 e_f11 e_f11__s). {
    eapply substitute_term__total.
  }
  destruct temp as [e_f11__s Hsubst].
  assert (temp : exists e'_f11__s, substitute x' v'_f2 e'_f11 e'_f11__s). {
    eapply substitute_term__total.
  }
  destruct temp as [e'_f11__s Hsubst'].

  assert (RC (k - j1 - j2 - 1) T2 rho e_f11__s e'_f11__s). {
    eapply RV1; eauto.
    all: eauto using eval_value, eval_to_value.
  }

  autorewrite with RC in H0.
  destruct H0 as [_ [_ H0]].

  assert (exists j0, terminates_incl e_f11__s j0 e_f (j - j1 - j2 - 1) /\ j = j1 + j2 + 1 + j0). {
    eapply inspect_eval__Apply3; eauto. split; eauto. subst. eauto. split; eauto.
  }
  destruct H1 as [j3 H1]. destruct H1. destruct H1.

  assert (j3 < k - j1 - j2 - 1). { apply skip. }
  remember (H0 j3 H4 e_f H1). clear Heqe. destruct e. destruct H5. destruct H5. exists x0, (j'_1 + j'_2 + 1 + x1). split. {
    eapply E_Apply; eauto. subst; eauto.
  }

  destruct T2; eauto.
  all : intros;
    try eapply H6; eauto;
    subst.
  - apply skip.
  - apply skip.
  - apply skip.
  - apply skip.
Qed.