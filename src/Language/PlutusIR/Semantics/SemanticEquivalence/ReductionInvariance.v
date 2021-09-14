Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.

Require Import Arith.

Lemma eval_preserves_termination : forall t v k j,
    terminates t k ->
    t =[j]=> v ->
    j < k ->
    terminates v k.
Proof. intros. exists v, 0.
  split.
  - apply eval_value. eapply eval_to_value. eassumption.
  - destruct (Nat.eq_0_gt_0_cases k).
    + subst. apply Nat.nlt_0_r in H1. destruct H1.
    + assumption.
Qed.

Lemma e : forall j k i,
    0 < k ->
    j < k - 0 ->
    j < k - i.
Proof. Admitted.

(** * Evaluation of terms preserves [R] (forward preservation) *)

(** ** Evaluation of the first related term preserves [R] *)

Lemma eval_preserves_R_left : forall k T t1 j1 v1 t2,
    terminates t1 k ->
    t1 =[j1]=> v1 ->
    j1 < k ->
    R k T t1 t2 ->
    R k T v1 t2.
Proof.
  intros k T t1 j1 v1 t2 Hterm_t1 Hev_t1 Hlt R.

  assert (emptyContext |-+ t1 : T) by eauto using R_typable_empty_1.
  assert (emptyContext |-+ t2 : T) by eauto using R_typable_empty_2.
  assert (emptyContext |-+ v1 : T) by eauto using preservation.

  autorewrite with R.
  destruct T.
  - apply R_impossible_type in R; auto. destruct R.
  - apply R_functional_extensionality in R as Hfe; auto.
    destruct Hfe as [v1' [v2 [j1' [j2 [Hlt_j1' [Hev_t1' [Hev_t2 Hfe]]]]]]].
  
    split; auto. split; auto.
    intros v0 j0 Hlt_j0 Hev_v1.
    exists v2, j2. split; auto.
    
    intros s1 s2 k' Hlt_k' R'. 
    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t1 as Hval_v1.
    apply eval_value in Hval_v1.
    unfold P_value in Hval_v1.
    assert (v0 = v1 /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst. 
    apply Hfe.
    + eapply e; eauto.
    + assumption.
  - (* Ty_IFix *)
    apply R_unwrap in R as Hunwr; auto.
    destruct Hunwr as [v1' [v2 [j1' [j2 [Hlt_j1' [Hev_t1' [Hev_t2 Hunwr]]]]]]].
    
    split; auto. split; auto.
    intros v0 j0 Hlt_j0 Hev_v1.
    exists v2, j2. split; auto.

    intros K k' Hlt_k' Hkind_T2.
    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t1 as Hval_v1.
    apply eval_value in Hval_v1 as Hev_v1'.
    unfold P_value in Hev_v1'.
    assert (v0 = v1 /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply Hunwr.
    + eapply e; eauto.
    + assumption.
  - (* Ty_Forall *)
    apply R_instantiational_extensionality in R as Hie; auto.
    destruct Hie as [v1' [v2 [j1' [j2 [Hlt_j1' [Hev_t1' [Hev_t2 Hie]]]]]]].

    split; auto. split; auto.
    intros v0 j0 Hlt_j0 Hev_v1.
    exists v2, j2. split; auto.

    intros t0_1 t0_2 T' k' Hlt_k' Heq1 Heq2 Hkind_T'.
    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t1 as Hval_v1.
    apply eval_value in Hval_v1 as Hev_v1'.
    unfold P_value in Hev_v1'.
    assert (TyAbs s k0 t0_1 = v1 /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    eapply Hie.
    + apply e; eauto.
    + reflexivity.
    + reflexivity.
    + assumption.
  - (* Ty_Builtin *)
    apply R_syntactic_equality in R as Hse; auto.
    destruct Hse as [v1' [v2 [j1' [j2 [Hlt_j1' [Hev_t1' [Hev_t2 Hse]]]]]]].
    subst.

    split; auto. split; auto.
    intros v0 j0 Hlt_j0 Hev_v1.
    exists v2, j2. split; auto.

    assert (v2 = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t1 as Hval_v1.
    apply eval_value in Hval_v1 as Hev_v1'.
    unfold P_value in Hev_v1'.
    assert (v0 = v1 /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    reflexivity.
  - (* Ty_Lam *)
    apply R_impossible_type in R; auto. destruct R.
  - (* Ty_App *)
    apply R_impossible_type in R; auto. destruct R.
Qed.

(** ** Evaluation of the second related term preserves [R] *)

Lemma eval_preserves_R_right : forall k T t1 t2 j2 v2,
    terminates t1 k ->
    t2 =[j2]=> v2 ->
    R k T t1 t2 ->
    R k T t1 v2.
Proof. 
  intros k T t1 t2 j2 v2 Hterm_t1 Hev_t2 R.

  assert (emptyContext |-+ t1 : T) by eauto using R_typable_empty_1.
  assert (emptyContext |-+ t2 : T) by eauto using R_typable_empty_2.
  assert (emptyContext |-+ v2 : T) by eauto using preservation.

  autorewrite with R.
  destruct T.
  - apply R_impossible_type in R; auto. destruct R.
  - apply R_functional_extensionality in R as Hfe; auto.
    destruct Hfe as [v1 [v2' [j1 [j2' [Hlt_j1 [Hev_t1 [Hev_t2' Hfe]]]]]]].
  
    split; auto. split; auto.
    intros v1' j1' Hlt_j1' Hev_t1'.

    assert (v2' = v2 /\ j2' = j2) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t2 as Hval_v2.
    apply eval_value in Hval_v2 as Hev_v2.
    unfold P_value in Hev_v2.

    exists v2, 0. split; auto.

    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hfe.
  - (* Ty_IFix *)
    apply R_unwrap in R as Hunwr; auto.
    destruct Hunwr as [v1 [v2' [j1 [j2' [Hlt_j1 [Hev_t1 [Hev_t2' Hunwr]]]]]]].

    split; auto. split; auto.
    intros v1' j1' Hlt_j1' Hev_t1'.

    assert (v2' = v2 /\ j2' = j2) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t2 as Hval_v2.
    apply eval_value in Hval_v2 as Hev_v2.
    unfold P_value in Hev_v2.

    exists v2, 0. split; auto.

    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hunwr.
  - (* Ty_Forall *)
    apply R_instantiational_extensionality in R as Hie; auto.
    destruct Hie as [v1 [v2' [j1 [j2' [Hlt_j1 [Hev_t1 [Hev_t2' Hie]]]]]]].

    split; auto. split; auto.
    intros v1' j1' Hlt_j1' Hev_t1'.

    assert (v2' = v2 /\ j2' = j2) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t2 as Hval_v2.
    apply eval_value in Hval_v2 as Hev_v2.
    unfold P_value in Hev_v2.

    exists v2, 0. split; auto.

    assert (v1' = v1 /\ j1' = j1) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hie.
  - (* Ty_Builtin *)
    apply R_syntactic_equality in R as Hse; auto.
    destruct Hse as [v1 [v2' [j1 [j2' [Hlt_j1 [Hev_t1 [Hev_t2' Hse]]]]]]].

    split; auto. split; auto.
    intros v1' j1' Hlt_j1' Hev_t1'.

    assert (v2' = v2 /\ j2' = j2) by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev_t2 as Hval_v2.
    apply eval_value in Hval_v2 as Hev_v2.
    unfold P_value in Hev_v2.

    exists v2, 0. split; auto.

    eapply eval__deterministic; eauto.
  - (* Ty_Lam *)
    apply R_impossible_type in R; auto. destruct R.
  - (* Ty_App *)
    apply R_impossible_type in R; auto. destruct R.
Qed.

(** ** Evaluation of both related terms preserves [R] *)

Lemma eval_preserves_R : forall k T t1 j1 v1 t2 j2 v2,
    terminates t1 k ->
    t1 =[j1]=> v1 ->
    j1 < k ->
    t2 =[j2]=> v2 ->
    R k T t1 t2 ->
    R k T v1 v2.
Proof.
  intros k T t1 j1 v1 t2 j2 v2 Hterm1 Hev1 Hlt1 Hev2 R.
  eapply eval_preserves_R_left; eauto.
  eapply eval_preserves_R_right; eauto.
Qed.



(** * Evaluation of terms preserved [R] (backward preservation) *)

(** ** Evaluation of the first related term preserved [R] *)

Lemma eval_preserved_R_left : forall k T t1 j1 v1 t2,
    emptyContext |-+ t1 : T ->
    terminates t1 k ->
    t1 =[j1]=> v1 ->
    j1 < k ->
    R k T v1 t2 ->
    R k T t1 t2.
Proof. Abort.

(** ** Evaluation of the second related term preserved [R] *)

Lemma eval_preserved_R_right : forall k T t1 t2 j2 v2,
    emptyContext |-+ t2 : T ->
    terminates t1 k ->
    t2 =[j2]=> v2 ->
    R k T t1 v2 ->
    R k T t1 t2.
Proof. Abort.

(** ** Evaluation of the both related terms preserved [R] *)

Lemma eval_preserved_R : forall k T t1 j1 v1 t2 j2 v2,
    emptyContext |-+ t1 : T ->
    emptyContext |-+ t2 : T ->
    terminates t1 k ->
    t1 =[j1]=> v1 ->
    j1 < k ->
    t2 =[j2]=> v2 ->
    R k T v1 v2 ->
    R k T t1 t2.
Proof.
  intros k T t1 j1 v1 t2 j2 v2 Htyp_t1 Htyp_t2 Hterm1 Hev1 Hlt1 Hev2 R.
  (*
  apply eval_preserved_R_left with v1; auto.
  apply eval_preserved_R_right with v2; auto.
  apply eval_preserves_termination with t1; auto.
  *)
Abort. 