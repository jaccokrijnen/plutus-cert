Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Local Open Scope string_scope.



Lemma RD_Rel : forall ck rho,
    RD ck rho ->
    forall X Chi T1 T2,
      sem rho X = Datatypes.Some Chi ->
      syn1 rho X = Datatypes.Some T1 ->
      syn2 rho X = Datatypes.Some T2 ->
      Rel T1 T2 Chi.
Proof.
  induction 1.
  - intros.
    unfold sem in H.
    inversion H.
  - intros.
    unfold sem in H3.
    unfold syn1 in H4.
    unfold syn2 in H5.
    destruct (X0 =? X) eqn:Heqb.
    + inversion H3. subst.
      inversion H4. subst.
      inversion H5. subst.
      assumption.
    + fold sem in H3.
      fold syn1 in H4.
      fold syn2 in H5.
      eapply IHRD; eauto.
Qed.

Lemma RD_sem_syn : forall ck rho,
    RD ck rho ->
    forall X Chi,
      sem rho X = Datatypes.Some Chi ->
      exists T1 T2, 
        syn1 rho X = Datatypes.Some T1 /\
        syn2 rho X = Datatypes.Some T2.
Proof.
  induction 1.
  - intros.
    unfold sem in H.
    inversion H.
  - intros.
    unfold sem in H3.
    simpl.
    destruct (X0 =? X) eqn:Heqb; eauto.
Qed.