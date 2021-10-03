Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

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
  - intros. apply skip.
Admitted.
    
Lemma RV_monotone : forall k rho T i v v',
    RV k T rho v v' ->  
    i <= k ->
    RV i T rho v v'.
Proof.
  intros k rho T i v v' HRV Hlt__i.
  destruct HRV as [Hval__v [Hval__v' HRC]].
  split. auto.
  split. auto.
  eapply RC_monotone. eauto. eauto.
Qed.

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
    eapply RV_monotone; eauto.
Qed. 