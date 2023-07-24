Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.

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

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    apply IHss.
Qed.

Lemma compatibility_Builtin: forall Delta Gamma f T Tn,
    T = lookupBuiltinTy f ->
    normalise T Tn ->
    LR_logically_approximate Delta Gamma (Builtin f) (Builtin f) Tn.
Proof with eauto_LR.
  intros Delta Gamma f Hlu Hnorm__Tn.
  unfold LR_logically_approximate.

  split...
  split...

  intros k rho env env' H_RD H_RG.
  subst.

  rewrite msubstA_Builtin. rewrite msubstA_Builtin.
  rewrite msubst_Builtin. rewrite msubst_Builtin.

  autorewrite with RC.
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f; subst.
(* ADMIT: We do not handle built-in functions yet. *)
Admitted.
