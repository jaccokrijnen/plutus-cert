Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.



Lemma compatibility_Constant : forall Delta Gamma u a,
    LR_logically_approximate Delta Gamma (Constant (Some (ValueOf u a))) (Constant (Some (ValueOf u a))) (Ty_Builtin (Some (TypeIn u))).
Proof with eauto_LR.
  intros Delta Gamma u a.
  unfold LR_logically_approximate.

  split...
  split...

  intros k rho env env' H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Constant. rewrite msubstA_Constant.
  rewrite msubst_Constant. rewrite msubst_Constant.
  rewrite msubstT_TyBuiltin. rewrite msubstT_TyBuiltin.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  exists (Constant (Some (ValueOf u a))), 0.
  split...

  split...
  split...

  left.

  split... intros Hcon. inversion Hcon.
  split... intros Hcon. inversion Hcon.
Qed.
