Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

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
    destruct (s =? x) eqn:Heqb.
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

Lemma compatibility_Var : forall Delta Gamma x T,
    Gamma x = Coq.Init.Datatypes.Some T ->
    LR_logically_approximate Delta Gamma (Var x) (Var x) T.
Proof with eauto_LR.
  intros Delta Gamma x T Hx.
  unfold LR_logically_approximate.

  split... split...

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  assert (forall x, (mupdate empty ct) x = lookup x ct). {
      intros. erewrite mupdate_lookup. auto.
    }
  subst.
  rewrite H in Hx.

  apply RC_lt.
  intros Hlt.

  destruct (RG_domains_match _ _ _ _ _ HRG _ _ Hx) as [v [v' [Hlu__v Hlu__v']]].
  destruct (RG_env_closed _ _ _ _ _ HRG) as [Hcls__env Hcls__env']...

  eapply RG_RV.
  - apply HRG.
  - apply Hx.
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v...
  - rewrite msubstA_Var.
    rewrite msubst_Var...
    rewrite Hlu__v'...
Qed.