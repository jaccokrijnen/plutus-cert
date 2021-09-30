Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.

Require Import Arith.

Lemma compatibility_LetNonRec : forall Delta Gamma bs t bs' t' T,
    forall Delta' Gamma',
      (Delta', Gamma') = append (flatten (List.map binds bs)) (Delta, Gamma) ->
      LR_logically_approximate Delta' Gamma' t t' T ->
      LR_logically_approximate_bindings_nonrec Delta Gamma bs bs' ->
      LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs' t') T.
Proof.
  intros Delta Gamma bs t bs' t' T Delta' Gamma' Hbinds IH_LR__t IH_LR__bs.
  unfold LR_logically_approximate.

  split. {
    eapply T_Let.
    - apply Hbinds.
    - eapply LR_la_bnr__oks in IH_LR__bs. 
      apply IH_LR__bs. 
    - apply IH_LR__t.  
  }

  split. {
    eapply T_Let.
    - eapply LR_la_bnr__oks in IH_LR__bs.
      destruct IH_LR__bs as [_ [_ Heq]].
      rewrite <- Heq.
      apply Hbinds.
    - eapply LR_la_bnr__oks in IH_LR__bs.
      apply IH_LR__bs.
    - apply IH_LR__t.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  (*
  intros e_sa e'_sa e_s e'_s.
  intros HmsA__e_sa HmsA__e'_sa Hms__e_s Hms__e'_s.

  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e_sa) as [eb_sa [HmsA__eb_sa Heq]].
  destruct (msubstA_LamAbs _ _ _ _ _ HmsA__e'_sa) as [eb'_sa [HmsA__eb'_sa Heq']].
  subst.
  destruct (msubst_LamAbs _ _ _ _ _ Hms__e_s) as [eb_s [Hms__eb_s Heq]].
  destruct (msubst_LamAbs _ _ _ _ _ Hms__e'_s) as [eb'_s [Hms__eb'_s Heq']].
  subst.

  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      destruct IH_LR.
      eapply T_LamAbs; eauto.
    - rewrite mupd_empty; eauto.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      destruct IH_LR. destruct H0.
      eapply T_LamAbs; eauto.
    - rewrite mupd_empty; eauto.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (LamAbs x (msubstT (msyn2 rho) T1) eb'_s).
  exists 0.
  split. {
    eapply eval_value. apply V_LamAbs.
  }
  intros.
  *)
Admitted.