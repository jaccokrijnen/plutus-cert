Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma msubst_Builtin : forall ss f t',
    msubst ss (Builtin f) t' ->
    t' = Builtin f.
Proof. 
  induction ss; intros.
  - inversion H. subst.
    reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    auto.
Qed.

Lemma msubstA_Builtin : forall ss f t',
    msubstA ss (Builtin f) t' ->
    t' = Builtin f.
Proof.
  induction ss; intros.
  - inversion H. subst.
    reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    auto.
Qed.

Lemma compatibility_Builtin: forall Delta Gamma f,
    LR_logically_approximate Delta Gamma (Builtin f) (Builtin f) (lookupBuiltinTy f).
Proof.
  intros Delta Gamma f.
  unfold LR_logically_approximate.

  split. { apply T_Builtin. }
  split. { apply T_Builtin. }
  
  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros HmsA__e_msa HmsA__e'_msa Hms__e_ms Hms__e'_ms.

  apply msubstA_Builtin in HmsA__e_msa as Heq.
  apply msubstA_Builtin in HmsA__e'_msa as Heq'. 
  subst.
  apply msubst_Builtin in Hms__e_ms as Heq.
  apply msubst_Builtin in Hms__e'_ms as Heq'.
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
  exists (Builtin f).
  exists 0.
  split. {
    eapply E_Builtin.
  }
  destruct f; simpl; intros; discriminate. (* TODO *)
Qed.