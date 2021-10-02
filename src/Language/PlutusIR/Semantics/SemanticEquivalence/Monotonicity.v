Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma e2 : forall j j0 k j1,
    j <= k ->
    j0 < j - j1 ->
    j0 < k - j1.
Proof. Admitted.

Lemma helper : forall i k j i0,
    i <= k ->
    i0 < i - j ->
    i0 < k - j.
Proof. Admitted. 

Lemma RC_monotone : forall k rho T i e e',
    RC k T rho e e' ->  
    i <= k ->
    RC i T rho e e'.
Proof.
  intros k rho T i e e' RC Hle__i.

  autorewrite with RC in RC.
  autorewrite with RC.

  destruct RC as [Htyp_e [Htyp_e' RC]].
  
  split; auto. split; auto.

  intros j Hlt__j e_f Hev__e.

  assert (j < k) by eauto using Nat.le_trans.

  remember (RC j H e_f Hev__e) as temp.
  clear Heqtemp. clear RC. rename temp into RC.

  destruct RC as [e'_f [j' [Hev__e' RV]]].

  exists e'_f, j'. split; auto.

  destruct T; try solve [eauto || intros; eapply RV; eauto using helper].
  - intros.
Admitted.
    
(*
Lemma RV_monotone : forall k T j v v',
    value v ->
    0 < k ->
    RC k T v v' ->  
    j <= k ->
    RC j T v v'.
Proof.
  intros k T j v v' Hval_v RC Hlt.

  eapply RC_monotone; eauto.
  split.
  - eapply eval_value. assumption.
  - assumption. 
Qed.*)

Lemma RG_monotone : forall c rho i k env env',
    RG rho k c env env' ->  
    i <= k ->
    RG rho i c env env'.
Proof.
  induction c.
  - intros.
    inversion H. 
    subst.
    constructor.
  - intros.
    inversion H.
    subst.
    eapply RG_cons; eauto.
    eapply RC_monotone; eauto.
Qed.