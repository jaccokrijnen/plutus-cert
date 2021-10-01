Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma msubst_Var : forall ss x,
    closed_env ss ->
    forall t',
      msubst_term ss (Var x) t' ->
        match lookup x ss with
        | Datatypes.Some t => t' = t
        | None=> t' = Var x
        end.
Proof. 
  induction ss; intros.
  - inversion H0. subst.
    reflexivity.
  - inversion H0. subst.
    simpl.
    inversion H3; subst.
    + rewrite String.eqb_refl.
      eapply msubst_closed; eauto.
      inversion H; auto.
    + apply String.eqb_neq in H2.
      rewrite H2.
      apply IHss; eauto.
      inversion H; auto.
Qed.

Lemma msubstA_Var : forall ss x t',
  msubstA ss (Var x) t' ->
  t' = Var x.
Proof.
  induction ss; intros.
  - inversion H. subst.
    reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    auto.
Qed.

Lemma compatibility_Var : forall Delta Gamma x T,
    Gamma x = Coq.Init.Datatypes.Some T ->
    LR_logically_approximate Delta Gamma (Var x) (Var x) T.
Proof.
  intros Delta Gamma x T Hx.
  unfold LR_logically_approximate.

  split. { apply T_Var. auto. }
  split. { apply T_Var. auto. }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_sa e'_sa e_s e'_s HmsA__e_sa HmsA__e'_sa Hms__e_s Hms__e'_s.

  assert (forall x, (mupdate empty ct) x = lookup x ct). {
      intros. erewrite mupdate_lookup. auto.
    }
  subst.
  rewrite H in Hx.

  destruct (RG_domains_match _ _ _ _ _ H_RG _ _ Hx) as [v [v' [Hlu__v Hlu__v']]].
  destruct (RG_env_closed _ _ _ _ _ H_RG) as [Hcls__env Hcls__env'].

  eapply RG_RC.
  - apply H_RG.
  - apply Hx.
  - apply msubstA_Var in HmsA__e_sa.
    subst.
    apply msubst_Var in Hms__e_s; eauto.
    rewrite Hlu__v in Hms__e_s.
    destruct Hms__e_s. subst.
    assumption.
  - apply msubstA_Var in HmsA__e'_sa.
    subst.
    apply msubst_Var in Hms__e'_s; eauto.
    rewrite Hlu__v' in Hms__e'_s.
    destruct Hms__e'_s. subst.
    assumption.
Qed.