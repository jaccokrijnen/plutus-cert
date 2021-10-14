Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.


Require Import Arith.

Lemma msubst_Error : forall ss T,
    msubst_term ss (Error T) = Error T.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Error : forall ss T,
    msubstA_term ss (Error T) = Error (msubstT ss T).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma compatibility_Error: forall Delta Gamma T,
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma (Error T) (Error T) T.
Proof with eauto_LR.
  intros Delta Gamma T Hkind__T.
  unfold LR_logically_approximate.

  split...
  split...
  
  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.
  
  autorewrite with RC.

  rewrite msubstA_Error. rewrite msubstA_Error.
  rewrite msubst_Error. rewrite msubst_Error.
  
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  exists (Error (msubstT (msyn2 rho) T)).
  exists 0.
  
  split. eapply E_Error...

  split. eapply T_Error. eapply msubstT_preserves_kinding_1...
  split. eapply T_Error. eapply msubstT_preserves_kinding_2...

  (* TODO: Actually handle errors in the relational model *)
Admitted.