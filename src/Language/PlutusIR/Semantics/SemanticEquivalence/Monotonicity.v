Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

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

Lemma RC_monotone : forall k T i e j e_f e',
    terminates_excl e j e_f k ->
    RC k T e e' ->  
    i <= k ->
    RC i T e e'.
Proof.
  intros k T i e j e_f e' Hterm RC Hle__i.
  
  destruct Hterm as [Hev__e Hlt__j] eqn:Hterm'.
  clear Hterm'.

  autorewrite with RC in RC.
  autorewrite with RC.

  destruct RC as [Htyp_e [Htyp_e' RC]].
  
  split; auto. split; auto.

  intros j0 Hlt__j0 e_f0 Hev__e0.

  assert (temp: e_f0 = e_f /\ j0 = j) by (eapply eval__deterministic; eauto).
  destruct temp. subst.
  clear Hev__e0 Hlt__j0.

  remember (RC j Hlt__j e_f Hev__e) as temp.
  clear Heqtemp. clear RC. rename temp into RC.

  destruct RC as [e'_f [j' [Hev__e' RV]]].

  exists e'_f, j'. split; auto.

  destruct T; try solve [eauto || intros; eapply RV; eauto using helper].
Qed.
    

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
Qed.