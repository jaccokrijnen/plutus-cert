Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.

Lemma msubst_Var : forall ss x,
    closed_env ss ->
    msubst_term ss (Var x) =
      match lookup x ss with
      | Datatypes.Some t => t
      | None => Var x
      end.
Proof. 
  induction ss; intros. 
  - reflexivity. 
  - intros. 
    destruct a. 
    simpl. 
    destruct (s =? x)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      destruct H.
      rewrite msubst_closed.
      all: auto.
    + apply eqb_neq in Heqb as Hneq.
      destruct H.
      eapply IHss.
      assumption.
Qed.

Lemma msubstA_Var : forall ss x,
    msubstA_term ss (Var x) = Var x.
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

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

  eapply RG_RV...
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v...
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v'...
Qed.
