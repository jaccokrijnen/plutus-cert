Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RD.Helpers.


Require Import Arith.
From Coq Require Import Lia.

Lemma RC_monotone : forall k rho T i e e' ck,
    RD ck rho ->
    RC k T rho e e' ->  
    i <= k ->
    RC i T rho e e'.
Proof with (try solve [eauto || lia]).
  intros k rho T i e e' ck HRD HRC Hle__i.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e.

  apply RC_to_RV with (j := j) (e_f := e_f) in HRC as temp...
  destruct temp as [e'_f [j' [Hev__e'_f HRV]]].

  exists e'_f, j'. split; auto.

  split. eapply RV_typable_empty_1...
  split. eapply RV_typable_empty_2...

  eapply RV_condition in HRV as HRV_cond...

  destruct HRV_cond as [HRV_cond | Herr]...

  destruct T; left.
  all: destruct HRV_cond as [Hnerr__e_f [Hnerr__e'_f HRV_cond]].
  all: split...
  all: split...
  - intros.
    apply RD_sem_syn with (ck := ck) in H as temp...
    destruct temp as [T1 [T2 [Hsyn1 Hsyn2]]].
    remember H as HRel. clear HeqHRel.
    apply RD_Rel with (ck := ck) (T1 := T1) (T2 := T2) in HRel...
    unfold Rel in HRel.
    apply HRel with (j := k - j)...
    eapply HRV_cond...
  - destruct HRV_cond as [x [e_body [e'_body [T1' [T1'a [Heq [Heq' Hfe]]]]]]].
    eexists. eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hfe...
  - destruct HRV_cond as [v_0 [v'_0 [F [F' [T [T' [Heq [Heq' Hunwr]]]]]]]].
    eexists. eexists. eexists. eexists. eexists. eexists.
    split... split...
    intros. eapply Hunwr...
  - destruct HRV_cond as [e_body [e'_body [Heq [Heq' Hie]]]].
    eexists. eexists.
    split... split...
    intros. eapply Hie...
Qed.
    
Lemma RV_monotone : forall k rho T i v v' ck,
    RD ck rho ->
    RV k T rho v v' ->  
    i <= k ->
    RV i T rho v v'.
Proof.
  intros k rho T i v v' ck HRD HRV Hlt__i.
  destruct HRV as [Hval__v [Hval__v' HRC]].
  split. auto.
  split. auto.
  eapply RC_monotone. eauto. eauto. eauto.
Qed.

Lemma RG_monotone : forall c ck rho i k env env',
    RD ck rho ->
    RG rho k c env env' ->  
    i <= k ->
    RG rho i c env env'.
Proof.
  induction c.
  - intros.
    inversion H0. 
    subst.
    constructor.
  - intros.
    inversion H0.
    subst.
    eapply RG_cons; eauto.
    eapply RV_monotone; eauto.
Qed. 