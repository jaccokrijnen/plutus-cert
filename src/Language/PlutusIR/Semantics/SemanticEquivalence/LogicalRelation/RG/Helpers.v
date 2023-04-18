Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.Util.List.

Local Open Scope list_scope.
Local Open Scope string_scope.



Lemma RG_extend_rho : forall X Chi T1 T2 rho k c env env' ,
    RG rho k c env env' ->
    RG ((X, (Chi, T1, T2)) :: rho) k c env env'.
Proof.
  intros.
  generalize dependent X.
  generalize dependent Chi.
  generalize dependent T1.
  generalize dependent T2.
  induction H; intros.
  - econstructor.
  - econstructor; eauto.
    apply RV_extend_rho.
    eauto.
Qed.

Lemma RG_domains_match : forall c e1 e2 k rho,
    RG rho k c e1 e2 ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      exists v1 v2,
        lookup x e1 = Datatypes.Some v1 /\
        lookup x e2 = Datatypes.Some v2.
Proof.
  intros c e1 e2 k rho V. 
  induction V; intros x0 T0 C.
  - discriminate.
  - simpl.
    simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + exists v1, v2. split; auto.
    + apply IHV with T0.
      assumption.
Qed.

Lemma RG_context_normal : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x T,
      lookup x c = Datatypes.Some T ->
      normal_Ty T.
Proof.
  intros c e1 e2 k rho V.
  induction V; intros x0 T0 C.
  - discriminate.
  - simpl in C.
    destruct (x =? x0) eqn:Heqb.
    + inversion C. subst.
      assumption.
    + eauto.
Qed.

Lemma RG_env_closed : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e1 /\ closed_env e2.
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V; intros.
  - split; reflexivity.
  - split.
    + simpl.
      split. 
      * eapply RV_typable_empty_1 in H; eauto.
        destruct H as [Tn [Hnorm__Tn Htyp__v1]].
        eapply typable_empty__closed.
        eauto.
      * apply IHV.
    + simpl.
      split.
      * eapply RV_typable_empty_2 in H; eauto.
        destruct H as [Tn' [Hnorm__Tn' Htyp__v2]].
        eapply typable_empty__closed.
        eauto.
    * apply IHV.
Qed.

Corollary RG_env_closed_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e1.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H H0). assumption. Qed.

Corollary RG_env_closed_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    closed_env e2.
Proof. intros. destruct (RG_env_closed _ _ _ _ _ H H0). assumption. Qed.

Lemma RG_RV : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x T v1 v2,
      lookup x c = Datatypes.Some T ->
      lookup x e1 = Datatypes.Some v1 ->
      lookup x e2 = Datatypes.Some v2 ->
      RV k T rho v1 v2.
Proof.
  intros rho k c e1 e2 V.
  induction V; intros x' T' v1' v2' G E1 E2.
  - destruct x'; discriminate.
  - simpl in G, E1, E2.
    destruct (x =? x').
    + inversion G. subst.
      inversion E1. subst.
      inversion E2. subst.
      assumption. 
    + apply IHV with x'; assumption.
Qed.

Lemma RG_drop : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    forall x,
      RG rho k (drop x c) (drop x e1) (drop x e2).
Proof.
  intros rho k c e1 e2 V.
  induction V.
  - intros. simpl. apply RG_nil.
  - intros. simpl.
    destruct (x =? x0).
    + apply IHV.
    + eapply RG_cons.
      * eassumption.
      * assumption.
      * assumption.
      * apply IHV.
Qed.
