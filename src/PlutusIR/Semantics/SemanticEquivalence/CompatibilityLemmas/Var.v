Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.

Lemma compatibility_Var : forall Delta Gamma x T Tn,
    lookup x Gamma = Coq.Init.Datatypes.Some T ->
    normalise T Tn ->
    LR_logically_approximate Delta Gamma (Var x) (Var x) Tn.
Proof with eauto_LR.
  intros Delta Gamma x T Tn Hx Hnorm__Tn.
  unfold LR_logically_approximate.

  split... split...

  intros k rho env env' HRD HRG.
  subst.

  apply RC_lt_obsolete.
  intros Hlt.

  destruct (RG_domains_match _ _ _ _ _ HRG _ _ Hx) as [v [v' [Hlu__v Hlu__v']]].
  destruct (RG_env_closed _ _ _ _ _ HRG) as [Hcls__env Hcls__env']...

  apply (RG_context_normal _ _ _ _ _ HRG) in Hx as Hnorm__T.
  eapply normalisation__stable in Hnorm__T...
  subst.

  eapply RG_RC...
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v...
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v'...
Qed.
