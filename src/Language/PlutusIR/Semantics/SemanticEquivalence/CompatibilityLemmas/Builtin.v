Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma msubst_Builtin : forall ss f,
    msubst_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Builtin : forall ss f,
    msubstA_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma compatibility_Builtin: forall Delta Gamma f,
    LR_logically_approximate Delta Gamma (Builtin f) (Builtin f) (lookupBuiltinTy f).
Proof.
  intros Delta Gamma f.
  unfold LR_logically_approximate.

  split. { apply T_Builtin. }
  split. { apply T_Builtin. }
  
  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
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

  rewrite msubstA_Builtin. rewrite msubstA_Builtin.
  rewrite msubst_Builtin. rewrite msubst_Builtin.
  

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (Builtin f).
  exists 0.
  
  split. {
    eapply E_Builtin.
  }

  destruct f; simpl; try discriminate.
  
  (* TODO: Builtins are not incorporated into the relational model *)
Admitted.