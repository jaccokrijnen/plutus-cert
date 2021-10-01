Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma msubst_Error : forall ss T t',
    msubst_term ss (Error T) t' ->
    t' = Error T.
Proof. 
  induction ss; intros.
  - inversion H. subst.
    reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    auto.
Qed.

Lemma msubstA_Error : forall ss T t',
    msubstA ss (Error T) t' ->
    exists T', T' = msubstT ss T /\ t' = Error T'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists T. auto.
  - inversion H. subst.
    inversion H2. subst.
    eauto.
Qed.

Lemma compatibility_Error: forall Delta Gamma T,
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma (Error T) (Error T) T.
Proof.
  intros Delta Gamma T Hkind__T.
  unfold LR_logically_approximate.

  split. { apply T_Error. assumption. }
  split. { apply T_Error. assumption. }
  
  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  destruct (msubstA_Error _ _ _ HmsA__e_msa) as [T' [HmsT__T' Heq]].
  destruct (msubstA_Error _ _ _ HmsA__e'_msa) as [T'' [HmsT__T'' Heq']].
  subst.
  apply msubst_Error in Hms__e_ms as Heq.
  apply msubst_Error in Hms__e'_ms as Heq'.
  subst.
  
  autorewrite with RC.
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }
  split. {
    replace emptyContext with (@empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      eauto with typing.
    - rewrite mupd_empty. reflexivity.
  }

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (Error (msubstT (msyn2 rho) T)).
  exists 0.
  split. {
    eapply E_Error.
  }
Admitted.