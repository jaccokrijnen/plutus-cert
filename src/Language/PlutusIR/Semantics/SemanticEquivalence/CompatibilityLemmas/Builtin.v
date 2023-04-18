Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.


Lemma compatibility_Builtin: forall Delta Gamma f T Tn,
    T = lookupBuiltinTy f ->
    normalise T Tn ->
    LR_logically_approximate Delta Gamma (Builtin f) (Builtin f) Tn.
Proof with eauto_LR.
  intros Delta Gamma f Hlu Hnorm__Tn.
  unfold LR_logically_approximate.

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  rewrite msubstA_Builtin. rewrite msubstA_Builtin.
  rewrite msubst_Builtin. rewrite msubst_Builtin.

  autorewrite with RC.
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f; subst.
(* ADMIT: We do not handle built-in functions yet. *)
Admitted.
