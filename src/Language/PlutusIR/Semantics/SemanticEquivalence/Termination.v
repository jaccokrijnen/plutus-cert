Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

Require Import Arith.

Definition terminates_excl__monotone : forall t1 j1 v1 k k',
    terminates_excl t1 j1 v1 k ->
    k <= k' ->
    terminates_excl t1 j1 v1 k'.
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - eapply Nat.le_trans; eauto.
Qed.

Definition terminates_excl__monotone' : forall t1 j1 v1 k k',
    terminates_excl t1 j1 v1 k ->
    k < k' ->
    terminates_excl t1 j1 v1 k'.
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - eapply Nat.lt_trans; eauto.
Qed.

Definition terminates_incl__monotone : forall t1 j1 v1 k k',
    terminates_incl t1 j1 v1 k ->
    k <= k' ->
    terminates_incl t1 j1 v1 k'.
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - eapply Nat.le_trans; eauto.
Qed.

Definition terminates_incl__monotone' : forall t1 j1 v1 k k',
    terminates_incl t1 j1 v1 k ->
    k < k' ->
    terminates_incl t1 j1 v1 k'.
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - eapply le_S in Hlt_j1. eapply le_trans; eauto.
Qed.



Definition terminates__excl_incl : forall t1 j1 v1 k,
    terminates_excl t1 j1 v1 (S k) ->
    terminates_incl t1 j1 v1 k.
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - apply le_S_n. assumption.
Qed.

Definition terminates__incl_excl : forall t1 j1 v1 k,
    terminates_incl t1 j1 v1 k ->
    terminates_excl t1 j1 v1 (S k).
Proof.
  intros.
  destruct H as [Hev_t1 Hlt_j1].
  split.
  - assumption.
  - eapply le_lt_trans; eauto.
Qed.

(*
Lemma termination_congr_Apply : forall t1 j1 v1 t2 k,
  terminates_excl (Apply t1 t2) k ->
  t1 =[j1]=> v1 ->
  terminates_excl (Apply v1 t2) (k-j1).
Proof.
  intros.
  destruct H as [v0 [j [Hlt_j]]].
  inversion Hlt_j.
  - subst.
    assert (v1 = LamAbs x T t4 /\ j1 = k1) by (eapply eval__deterministic; eauto).
    destruct H1. subst.
    exists v0, (0 + k2 + 1 + k0).
    split.
    + eapply E_Apply.
      * eapply eval_value.
        constructor.
      * eauto.
      * eauto.
      * eauto.
    + simpl.
Admitted.
*)

Lemma termination_congr_Apply1 : forall t1 t2 j v0,
    Apply t1 t2 =[j]=> v0 ->
    exists v1 j1, terminates_incl t1 j1 v1 j.
Proof.
  intros.
  inversion H. all: subst.
  - exists (LamAbs x T t4).
    exists k1.
    split; auto.
Admitted.

Lemma termination_congr_Apply2 : forall t1 t2 j v0 j1 v1,
    Apply t1 t2 =[j]=> v0 ->
    terminates_incl t1 j1 v1 j ->
    exists v2 j2, terminates_incl t2 j2 v2 (j - j1).
Proof. 
  intros. 
  destruct H0.
  inversion H.
  all: subst.
  - assert (v1 = LamAbs x T t4 /\ j1 = k1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    exists v2.
    exists k2.
    split; auto.
Admitted.

Lemma termination_congr_Apply3 : forall t1 t2 j v0 j1 x T t0 j2 v2 t0',
    Apply t1 t2 =[j]=> v0 ->
    terminates_incl t1 j1 (LamAbs x T t0) j ->
    terminates_incl t2 j2 v2 (j - j1) ->
    substitute x v2 t0 t0' ->
    exists j0, terminates_incl t0' j0 v0 (j - j1 - j2 - 1) /\ j = j1 + j2 + 1 + j0.
Proof. 
  intros. 
  destruct H0.
  destruct H1.
  inversion H.
  all: subst.
  - assert (LamAbs x0 T0 t5 = LamAbs x T t0 /\ k1 = j1) by (eapply eval__deterministic; eauto).
    destruct H5. inversion H5. subst.
    assert (v1 = v2 /\ k2 = j2) by (eapply eval__deterministic; eauto).
    destruct H6. subst.
    assert (t0'0 = t0') by (eapply substitute__deterministic; eauto).
    subst.
    exists k0.
    split; auto.
    split; auto.
Admitted.