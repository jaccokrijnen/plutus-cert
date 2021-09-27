Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma eval_preserves_termination : forall t v k j,
    terminates_excl t j v k ->
    terminates_excl v 0 v k.
Proof. 
  intros.
  destruct H.
  split.
  - apply eval_value. eapply eval_to_value. eassumption.
  - destruct (Nat.eq_0_gt_0_cases k).
    + subst. apply Nat.nlt_0_r in H0. destruct H0.
    + assumption.
Qed.

Lemma helper : forall j k i,
    0 < k ->
    j < k - 0 ->
    j < k - i.
Proof. Admitted.

(** * Evaluation of terms preserves [R] (forward preservation) *)

(** ** Evaluation of the first related term preserves [R] *)

Lemma eval_preserves_R_left : forall k T rho e j e_f e',
    terminates_excl e j e_f k ->
    RC k T rho e e' ->
    RC k T rho e_f e'.
Proof. (*
  intros k T e j e_f e' Hterm RC.
  destruct Hterm as [Hev__e Hlt__j] eqn:Hterm'.

  assert (emptyContext |-+ e : T) by eauto using RC_typable_empty_1.
  assert (emptyContext |-+ e' : T) by eauto using RC_typable_empty_2.
  assert (emptyContext |-+ e_f : T) by eauto using preservation.

  autorewrite with RC.
  destruct T.
  - (* Ty_Var *)
    eapply RC_impossible_type in RC; eauto. destruct RC.

  - (* Ty_Fun *)
    eapply RC_functional_extensionality in RC as Hfe; eauto.
    destruct Hfe as [e'_f [j' [Hev__e' Hfe]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.
    exists e'_f, j'. split; auto.

    intros x e_body x' e'_body Heq1 Heq2 i Hlt__i  v v' e_body' e'_body' RC' Hsubst Hsubst'.

    apply eval_to_value in Hev__e as Hval__e_f.
    apply eval_value in Hval__e_f.
    unfold P_value in Hval__e_f.
    assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst. 

    eapply Hfe.
    + reflexivity.
    + reflexivity.
    + eapply helper; eauto.
    + eassumption.
    + assumption.
    + assumption.

  - (* Ty_IFix *)
    eapply RC_unwrap in RC as Hunwr; eauto.
    destruct Hunwr as [e'_f [j' [Hev__e' Hunwr]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.
    exists e'_f, j'. split; auto.

    intros v v' Heq1 Heq2 i Hlt__i K Hkind_T2.

    apply eval_to_value in Hev__e as Hval__e_f.
    apply eval_value in Hval__e_f.
    unfold P_value in Hval__e_f.
    assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst. 

    apply Hunwr.
    + reflexivity.
    + reflexivity.
    + eapply helper; eauto.
    + assumption.

  - (* Ty_Forall *)
    eapply RC_instantiational_extensionality in RC as Hie; eauto.
    destruct Hie as [e'_f [j' [Hev__e' Hie]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.
    exists e'_f, j'. split; auto.

    intros e_body e'_body Heq1 Heq2 Hi Hlt__i T2.

    apply eval_to_value in Hev__e as Hval__e_f.
    apply eval_value in Hval__e_f.
    unfold P_value in Hval__e_f.
    assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst. 

    eapply Hie.
    + reflexivity.
    + reflexivity.
    + apply helper; eauto.

  - (* Ty_Builtin *)
    eapply RC_syntactic_equality in RC as Hse; eauto.
    destruct Hse as [e'_f [j' [Hev__e' Hse]]].
    subst.

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.
    exists e'_f, j'. split; auto.

    intros v v' sv sv' Heq1 Heq2 Heq3 Heq4.

    apply eval_to_value in Hev__e as Hval__e_f.
    apply eval_value in Hval__e_f.
    unfold P_value in Hval__e_f.
    assert (e_f0 = e_f /\ j0 = 0) by (eapply eval__deterministic; eauto).
    destruct H2. subst. 

    eapply Hse; auto.

  - (* Ty_Lam *)
    eapply RC_impossible_type in RC; eauto. destruct RC.

  - (* Ty_App *)
    eapply RC_impossible_type in RC; eauto. destruct RC.
Qed.*)
Admitted.

(** ** Evaluation of the second related term preserves [R] *)

(*
Lemma eval_preserves_R_left : forall k T e j e_f e',
    terminates_excl e j e_f k ->
    RC k T e e' ->
    RC k T e_f e'.
Proof.
  intros k T e j e_f e' Hterm RC.
  destruct Hterm as [Hev__e Hlt__j] eqn:Hterm'.
  assert (emptyContext |-+ e : T) by eauto using RC_typable_empty_1.
  assert (emptyContext |-+ e' : T) by eauto using RC_typable_empty_2.
  assert (emptyContext |-+ e_f : T) by eauto using preservation.
  autorewrite with RC.
  destruct T.
  - (* Ty_Var *)
    eapply RC_impossible_type in RC; eauto. destruct RC.*)

Lemma eval_preserves_R_right : forall k T rho e j e_f e' j' e'_f,
    terminates_excl e j e_f k ->
    e' =[j']=> e'_f ->
    RC k T rho e e' ->
    RC k T rho e e'_f.
Proof. (*
  intros k T e j e_f e' j' e'_f Hterm Hev__e' RC.
  destruct Hterm as [Hev__e Hlt__j] eqn:Hterm'.

  assert (emptyContext |-+ e : T) by eauto using RC_typable_empty_1.
  assert (emptyContext |-+ e' : T) by eauto using RC_typable_empty_2.
  assert (emptyContext |-+ e'_f : T) by eauto using preservation.

  autorewrite with RC.
  destruct T.
  - (* Ty_Var *)
    eapply RC_impossible_type in RC; eauto. destruct RC.

  - (* Ty_Fun *)
    eapply RC_functional_extensionality in RC as Hfe; eauto.
    destruct Hfe as [e'_f0 [j'0 [Hev__e'0 Hfe]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.

    assert (e'_f0 = e'_f /\ j'0 = j') by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev__e' as Hval__e'_f.
    apply eval_value in Hval__e'_f.
    unfold P_value in Hval__e'_f.
    exists e'_f, 0. split; auto.

    assert (e_f0 = e_f /\ j0 = j) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hfe.

  - (* Ty_IFix *)
    eapply RC_unwrap in RC as Hunwr; eauto.
    destruct Hunwr as [e'_f0 [j'0 [Hev__e'0 Hunwr]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.

    assert (e'_f0 = e'_f /\ j'0 = j') by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev__e' as Hval__e'_f.
    apply eval_value in Hval__e'_f.
    unfold P_value in Hval__e'_f.
    exists e'_f, 0. split; auto.

    assert (e_f0 = e_f /\ j0 = j) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hunwr.

  - (* Ty_Forall *)
    eapply RC_instantiational_extensionality in RC as Hie; eauto.
    destruct Hie as [e'_f0 [j'0 [Hev__e'0 Hie]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.

    assert (e'_f0 = e'_f /\ j'0 = j') by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev__e' as Hval__e'_f.
    apply eval_value in Hval__e'_f.
    unfold P_value in Hval__e'_f.
    exists e'_f, 0. split; auto.

    assert (e_f0 = e_f /\ j0 = j) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hie.

  - (* Ty_Builtin *)
    eapply RC_syntactic_equality in RC as Hse; eauto.
    destruct Hse as [e'_f0 [j'0 [Hev__e'0 Hse]]].

    split; auto. split; auto.
    intros j0 Hlt__j0 e_f0 Hev__e_f.

    assert (e'_f0 = e'_f /\ j'0 = j') by (eapply eval__deterministic; eauto).
    destruct H2. subst.
    apply eval_to_value in Hev__e' as Hval__e'_f.
    apply eval_value in Hval__e'_f.
    unfold P_value in Hval__e'_f.
    exists e'_f, 0. split; auto.

    assert (e_f0 = e_f /\ j0 = j) by (eapply eval__deterministic; eauto).
    destruct H2. subst.

    apply Hse.

  - (* Ty_Lam *)
    eapply RC_impossible_type in RC; eauto. destruct RC.

  - (* Ty_App *)
    eapply RC_impossible_type in RC; eauto. destruct RC.
Qed.*)
Admitted.

(** ** Evaluation of both related terms preserves [R] *)

Lemma eval_preserves_R : forall k T rho e j e_f e' j' e'_f,
    terminates_excl e j e_f k ->
    e' =[j']=> e'_f ->
    RC k T rho e e' ->
    RC k T rho e_f e'_f.
Proof.
  intros k T rho e j e_f e' j' e'_f Hterm Hev RC.
  eapply eval_preserves_R_left; eauto.
  eapply eval_preserves_R_right; eauto.
Qed.

(*
(** * Evaluation of terms preserved [R] (backward preservation) *)

(** ** Evaluation of the first related term preserved [R] *)

Lemma eval_preserved_R_left : forall k T e j e_f e',
    emptyContext |-+ e : T ->
    terminates_excl e j e_f k ->
    RC k T e_f e' ->
    RC k T e e'.
Proof. Abort.

(** ** Evaluation of the second related term preserved [R] *)

Lemma eval_preserved_R_right : forall k T e j e_f e' j' e'_f,
    emptyContext |-+ e' : T ->
    terminates_excl e j e_f k ->
    e' =[j']=> e'_f ->
    RC k T e e'_f ->
    RC k T e e'.
Proof. Abort.

(** ** Evaluation of the both related terms preserved [R] *)

Lemma eval_preserved_R : forall k T e j e_f e' j' e'_f,
    emptyContext |-+ e : T ->
    emptyContext |-+ e' : T ->
    terminates_excl e j e_f k ->
    e' =[j']=> e'_f ->
    RC k T e_f e'_f ->
    RC k T e e'.
Proof.
  intros k T e j e_f e' j' e'_f Htyp__e Htyp__e' Hterm Hev RC.
  (*
  apply eval_preserved_R_left with v1; auto.
  apply eval_preserved_R_right with v2; auto.
  apply eval_preserves_termination with t1; auto.
  *)
Abort.  
*)