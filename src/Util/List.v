Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations.
Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if j =? k then Datatypes.Some x else lookup k l'
  end.

Lemma lookup_eq {X} k (v : X) kvs : lookup k ((k, v) :: kvs) = Some v.
Proof.
  simpl.
  destruct (k =? k) eqn:H_eqb.
  - reflexivity.
  - rewrite eqb_neq in H_eqb.
    contradiction.
Qed.

Lemma lookup_neq {X} k1 k2 (v : X) kvs : k1 <> k2 -> lookup k1 ((k2, v) :: kvs) = lookup k1 kvs.
Proof with auto.
  intros H_neq.
  simpl.
  rewrite eqb_sym.
  rewrite <- eqb_neq in H_neq.
  rewrite H_neq...
Qed.

Lemma In__lookup_append {X : Type} k (kvs : list (string * X)) ys zs :
  In k (map fst kvs) ->
  lookup k (kvs ++ ys) = lookup k (kvs ++ zs).
Proof.
  intros H_In.
  induction kvs.
  - inversion H_In.
  - destruct a.
    destruct (string_dec k s); subst.
    + simpl.
      assert (H : s =? s = true). { rewrite eqb_eq. reflexivity. }
      rewrite H.
      reflexivity.
    + simpl.
      assert (H : s =? k = false). { rewrite -> eqb_sym. rewrite eqb_neq. assumption. }
      rewrite H.
      destruct H_In.
        * destruct H0. contradiction.
        * auto.
Qed.

Lemma notIn__lookup_append {X : Type} k (kvs : list (string * X)) ys :
     ~ In k (map fst ys) -> lookup k (ys ++ kvs) = lookup k kvs.
Proof with auto.
  intros H_notIn.
  induction ys...
  destruct a.
  simpl in H_notIn.
  destruct (string_dec s k).
  - assert (s = k \/ In k (map fst ys)) by auto.
    contradiction.
  - rewrite <- eqb_neq in n.
    simpl.
    rewrite n.
    assert (~ In k (map fst ys))...
Qed.

Lemma lookup_append_cong {X : Type} k (new kvs kvs' : list (string * X)) :
  lookup k kvs = lookup k kvs' -> 
  lookup k (new ++ kvs) = lookup k (new ++ kvs').
Proof with auto.
  intros H_kvs_kvs'.
  induction new...
  - destruct a.
    destruct (eqb s k) eqn:H_eqb.
    all: simpl; rewrite H_eqb...
Qed.

Definition inclusion {A : Type} (m m' : list (string * A)) :=
  forall x v, lookup x m = Some v -> lookup x m' = Some v.

Lemma inclusion_tail {A : Type} (x : string * A) m m' :
  inclusion m m' ->
  inclusion (x :: m) (x :: m').
Proof.
  intro H_incl.
  destruct x.
  intros k v.
  destruct (s =? k) eqn:H_eqb.
  all: simpl; rewrite H_eqb; auto.
Qed.

Lemma inclusion_refl {A} (xs : list (string * A)) :
  inclusion xs xs.
Proof with auto.
  unfold inclusion.
  intros.
  induction xs...
Qed.

Lemma inclusion_trans : forall A (m1 m2 m3 : list (string * A)), inclusion m1 m2 ->
  inclusion m2 m3 -> inclusion m1 m3.
Proof with auto.
  unfold inclusion...
Qed.

Lemma inclusion_cons A (m m' : list (string * A)) x vx :
  inclusion m m' -> inclusion ((x, vx) :: m) ((x, vx) :: m').
Proof with auto.
  intros H_incl.
  unfold inclusion.
  intros y vy H_lookup_y.
  destruct (eqb x y) eqn:H_eqb.
  all: simpl in *; rewrite H_eqb in *...
Qed.

Lemma inclusion_append {A} m m' (kvs : list (string * A)) :
  inclusion m m' -> inclusion (kvs ++ m) (kvs ++ m').
Proof with auto.
  intros H_incl.
  induction kvs...
  unfold inclusion. intros.
  destruct a.
  destruct (eqb s x) eqn:H_eqb.
  all: simpl in *;
    rewrite H_eqb in *...
Qed.

Lemma cons_shadow {A} k (x y : A) xs:
  inclusion ((k, x) :: (k, y) :: xs) ((k, x) :: xs).
Proof with auto.
  unfold inclusion.
  intros l w H_lookup.
  simpl in *.
  destruct (k =? l) eqn:H_eqb...
Qed.

Lemma append_shadow {A} k (v : A) xs ys :
  In k (map fst xs) -> inclusion (xs ++ ((k, v) :: ys)) (xs ++ ys).
Proof.
Admitted.

Lemma cons_permute A (m : list (string * A)) x1 x2 v1 v2 :
  x2 <> x1 -> inclusion ((x1, v1) :: (x2 , v2) :: m) ((x2, v2) :: (x1, v1) :: m).
Proof with auto.
  unfold inclusion.
  intros H_neq x v.
  destruct (x1 =? x) eqn:H_x_x1;
  destruct (x2 =? x) eqn:H_x_x2.
  all: try (simpl; rewrite H_x_x1, H_x_x2; auto).
  assert (x2 = x1).
    { rewrite -> eqb_eq in *.
      apply eq_sym in H_x_x2. 
      transitivity x...
    }
  contradiction.
Qed.

Lemma append_permute A (m : list (string * A)) k (v : A) xs ys:
  ~ (In k (map fst xs)) -> inclusion (xs ++ ((k, v) :: ys)) ((k, v) :: xs ++ ys) .
Admitted.

Definition equivalent {A : Type} (m m' : list (string * A)) :=
  inclusion m m' /\ inclusion m' m.

Lemma equivalent_refl : forall A (m : list (string * A)), equivalent m m.
Proof.
  unfold equivalent.
  auto using inclusion_refl.
Qed.

Lemma equivalent_sym : forall A (m m' : list (string * A)), equivalent m m' -> equivalent m' m.
Proof.
  unfold equivalent, inclusion.
  intros.
  easy.
Qed.

Lemma equivalent_trans : forall A (m1 m2 m3 : list (string * A)), equivalent m1 m2 ->
  equivalent m2 m3 -> equivalent m1 m3.
Proof.
  unfold equivalent, inclusion.
  intros.
  destruct H, H0.
  auto.
Qed.

Require Import Coq.Classes.RelationClasses.

Global Instance inclusion_reflexive : forall (A : Type), Reflexive (@inclusion A) := @inclusion_refl.
Global Instance inclusion_transitive : forall (A : Type), Transitive (@inclusion A) := inclusion_trans.

Global Instance equivalent_reflexive : forall (A : Type), Reflexive (@equivalent A) := equivalent_refl.
Global Instance equivalent_symmetric : forall (A : Type), Symmetric (@equivalent A) := equivalent_sym.
Global Instance equivalent_transitive : forall (A : Type), Transitive (@equivalent A) := equivalent_trans.
Global Instance equivalent_equivalence : forall (A : Type), Equivalence (@equivalent A) := { }.

(*
Add Parametric Relation (A : Type) : (list (string * A)) (equivalent)
  reflexivity proved by (equivalent_refl A)
  symmetry proved by (equivalent_sym A)
  transitivity proved by (equivalent_trans A) as tests.

Definition my_setoid : Setoid := _.
Global Instance equivalent_Setoid : forall (A : Type), Setoid (@equivalent A) := _.
*)


Fixpoint lookup' {A X : Type} (A_eqb : A -> A -> bool) (k : A) (l : list (A * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if A_eqb j k then Datatypes.Some x else lookup' A_eqb k l'
  end.

Inductive Lookup {A B :Type} (k : A) (v : B) : list (A * B) -> Prop :=
  | Here    : forall {kvs}, Lookup k v ((k, v) :: kvs)
  | There   : forall {k' v' kvs}, ~ (k = k') -> Lookup k v kvs -> Lookup k v ((k', v') :: kvs)
.

Lemma Lookup_lookup : forall A k (v : A) kvs, Lookup k v kvs <-> lookup k kvs = Some v.
Admitted.


Definition inclusion_empty (A : Type) (m : list (string * A)) : inclusion [] m.
Proof.
  unfold inclusion. intros. inversion H.
Qed.



Lemma Lookup_functional : forall A B (k : A) (v v' : B) kvs,  Lookup k v kvs -> Lookup k v' kvs -> v = v'.
Admitted.

Lemma Lookup_unique : forall A B (k : A) (v : B) kvs (P P' : Lookup k v kvs), P = P'.
Admitted.

Lemma Lookup_In : forall A B (k : A) (v : B) kvs, NoDup kvs -> In (k, v) kvs <-> Lookup k v kvs.
Admitted.

Fixpoint drop {X:Type} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | (n',x) :: nxs' => if n' =? n then drop n nxs' else (n',x) :: (drop n nxs')
  end.

Fixpoint mdrop {X:Type} (ns : list string) (nxs: list (string * X)) : list (string * X) :=
  match ns with
  | nil => nxs
  | n :: ns' =>
      mdrop ns' (drop n nxs) 
  end.

Definition forall2b {A} (p : A -> A -> bool) := fix f xs ys :=
  match xs, ys with
    | []       , []        => true
    | (x :: xs), (y :: ys) => (p x y && f xs ys)%bool
    | _        , _         => false
  end.




Lemma mdrop_nil : forall X ns,
    @mdrop X ns nil = nil.
Proof. induction ns; auto. Qed.

Definition elem {A} (A_eqb : A -> A -> bool) (x : A) (xs : list A) :=
  match find (A_eqb x) xs with
    | None   => false
    | Some _ => true
  end.
