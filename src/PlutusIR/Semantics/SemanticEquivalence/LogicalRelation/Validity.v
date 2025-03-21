Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RD.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.

Require Import Lia.


Lemma validity : forall ck rho T,
    RD ck rho ->
    Rel (msubstT (msyn1 rho) T) (msubstT (msyn2 rho) T) (fun k e e' => RV k T rho e e').
Proof with (try solve [eauto with typing || lia]).
  intros.
  unfold Rel.
  intros.
  split. apply H0.
  split. apply H0.
  apply RV_typable_empty in H0 as H2...
  destruct H2. destruct H2. destruct H2.
  destruct H3. destruct H3.
  split... split...
  intros.
  eapply RV_monotone...
Qed.


Lemma validity' : forall Δ ρ T,
    D Δ ρ ->
    Rel' (msubstT (msyn1 ρ) T) (msubstT (msyn2 ρ) T) (fun k e e' => V k T ρ e e').
Proof with (try solve [eauto with typing || lia]).
  intros.
  split. apply V_value in H0. apply H0.
  split. apply V_value in H0. apply H0.
  apply V_typable_empty in H0 as H2...
  destruct H2. destruct H2. destruct H2.
  split... split...
  intros.
  eapply V_monotone...
Qed.
