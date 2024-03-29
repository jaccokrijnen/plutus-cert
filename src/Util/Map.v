From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A} (m : total_map A) (x : string) (v : A) :=
  fun x' => if x =? x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).



Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. intros. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) (x : string) (v : A),
    (x !-> v ; m) x = v.
Proof. intros. unfold t_update. rewrite eqb_refl. reflexivity. Qed.

Lemma t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v; m) x2 = m x2.
Proof. intros. unfold t_update. destruct (x1 =? x2) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq. apply H in Heq as Hcon. destruct Hcon.
  - reflexivity.
Qed.

Theorem t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (x =? x0) eqn:Heqb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x; m) = m.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold t_update.
  destruct (x =? x0) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (x1 =? x) eqn:Heqb1; destruct (x2 =? x) eqn:Heqb2.
  - apply eqb_eq in Heqb1 as Heq1.
    apply eqb_eq in Heqb2 as Heq2.
    symmetry in Heq1.
    remember (eq_trans Heq2 Heq1).
    clear Heqe.
    apply H in e.
    destruct e.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.



Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Lemma update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H.
Qed.

Theorem update_shadow :  forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.



Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
    inclusion m m' ->
    inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold inclusion.
  intros A m m' x vx H.
  intros y vy.
  destruct (x =? y) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    rewrite Heq.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - apply eqb_neq in Heqb as Hneq.
    rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hneq.
    + apply Hneq.
Qed.

Lemma inclusion_empty : forall (A : Type) (m : partial_map A),
    inclusion empty m.
Proof.
  intros.
  unfold inclusion.
  intros.
  inversion H.
Qed.

Lemma inclusion_refl : forall (A : Type) (m : partial_map A),
    inclusion m m.
Proof.
  intros.
  unfold inclusion.
  intros.
  assumption.
Qed.