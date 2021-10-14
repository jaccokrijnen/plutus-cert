Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

From Coq Require Import Lia.
From Coq Require Import Arith.

Lemma msubst_Apply : forall ss t1 t2,
    msubst_term ss (Apply t1 t2) = Apply (msubst_term ss t1) (msubst_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Apply : forall ss t1 t2,
    msubstA_term ss (Apply t1 t2) = Apply (msubstA_term ss t1) (msubstA_term ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma compatibility_Apply : forall Delta Gamma e1 e2 e1' e2' T1 T2 ,
    LR_logically_approximate Delta Gamma e1 e1' (Ty_Fun T1 T2) ->
    LR_logically_approximate Delta Gamma e2 e2' T1 ->
    LR_logically_approximate Delta Gamma (Apply e1 e2) (Apply e1' e2') T2.
Proof with eauto_LR.
  intros Delta Gamma e1 e2 e1' e2' T1 T2 IH_LR1 IH_LR2.
  unfold LR_logically_approximate.

  destruct IH_LR1 as [Htyp__e1 [Htyp__e1' IH1]].
  destruct IH_LR2 as [Htyp__e2 [Htyp__e2' IH2]].

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.
  
  rewrite msubstA_Apply. rewrite msubstA_Apply. 
  rewrite msubst_Apply. rewrite msubst_Apply.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f; subst.
  - (* E_Apply *)
    rename v2 into e_f2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j0 into j_3.

    assert (HRC1 : 
      RC k (Ty_Fun T1 T2) rho 
        (msubst_term env (msubstA_term (msyn1 rho) e1)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e1'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := LamAbs x T t0) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].

    assert (k - j_1 <= k)...
    assert (HRC2 : 
      RC (k - j_1) T1 rho 
        (msubst_term env (msubstA_term (msyn1 rho) e2)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e2'))
    ) by eauto using RG_monotone.
    clear H.

    apply RC_to_RV  with (j := j_2) (e_f := e_f2) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_functional_extensionality in HRV1 as temp...

    destruct temp as [temp | temp].
    + destruct temp as [x0 [e_body [ x0' [e'_body [Heq [Heq' Hfe]]]]]].
      inversion Heq. subst. clear Heq.

      apply RV_monotone with (i := k - j_1 - j_2 - 1) (ck := ck)  in HRV2...

      apply Hfe with (i := k - j_1 - j_2 - 1) in HRV2 as HRC0...

      assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
      rewrite H.
      clear H.

      apply RC_to_RV with (j := j_3) (e_f := e_f) in HRC0 as temp...
      destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

      eexists. eexists. 
      split. eapply E_Apply...

      split. eapply RV_typable_empty_1...
      split. eapply RV_typable_empty_2...

      eapply RV_condition...
    + destruct temp as [f [args [f' [args' [H _]]]]]. inversion H.
  - (* E_ApplyExtBuiltin *)
    rename v2 into e_f2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j3 into j_3.

    assert (HRC1 : 
      RC k (Ty_Fun T1 T2) rho 
        (msubst_term env (msubstA_term (msyn1 rho) e1)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e1'))
    ) by eauto.

    eapply RC_to_RV with (j := j_1) (e_f := ExtBuiltin f args) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].

    assert (k - j_1 <= k)...
    assert (HRC2 : 
      RC (k - j_1) T1 rho 
        (msubst_term env (msubstA_term (msyn1 rho) e2)) 
        (msubst_term env' (msubstA_term (msyn2 rho) e2'))
    ) by eauto using RG_monotone.
    clear H.

    apply RC_to_RV  with (j := j_2) (e_f := e_f2) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_functional_extensionality in HRV1 as temp...

    destruct temp as [temp | temp].
    + destruct temp as [x0 [e_body [ x0' [e'_body [Heq [Heq' Hfe]]]]]].
      inversion Heq.
    + destruct temp as [f0 [args0 [f0' [args0' [Heq [Heq' Hfe]]]]]].
      inversion Heq. inversion Heq'. subst. clear H. 

      apply RV_monotone with (i := k - j_1 - j_2 - 1) (ck := ck) in HRV2...

      apply Hfe with (i := k - j_1 - j_2 - 1) in HRV2 as HRC0...

      assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
      rewrite H.
      clear H.

      apply RC_to_RV with (j := j_3) (e_f := e_f) in HRC0 as temp...
      destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

      eexists. eexists. 
      split. eapply E_ApplyExtBuiltin...

      split. eapply RV_typable_empty_1...
      split. eapply RV_typable_empty_2...

      eapply RV_condition...
  - (* E_IfCondition *)
    apply skip.
  - (* E_IfThenBranch *)
    apply skip.
  - (* E_IfTrue *)
    apply skip.
  - (* E_IfFalse *)
    apply skip.
Admitted.