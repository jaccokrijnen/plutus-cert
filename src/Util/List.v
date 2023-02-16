From Coq Require Import
  Strings.String
  Lists.List.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.

Fixpoint lookup {X:Type} (k : string) (l : list (string * X)) : option X :=
  match l with
  | nil => None
  | (j,x) :: l' => if j =? k then Datatypes.Some x else lookup k l'
  end.

Inductive Lookup {A B :Type} (k : A) (v : B) : list (A * B) -> Prop :=
  | Here    : forall {kvs}, Lookup k v ((k, v) :: kvs)
  | There   : forall {k' v' kvs}, ~ (k = k') -> Lookup k v kvs -> Lookup k v ((k', v') :: kvs)
.

#[export] Hint Constructors Lookup : core.

Lemma Lookup_lookup : forall A k (v : A) kvs, Lookup k v kvs <-> lookup k kvs = Some v.
Proof.
  intros. generalize dependent k. generalize dependent v.
  induction kvs; split; intros; simpl; inversion H.
    - rewrite eqb_refl. reflexivity.
    - rewrite eqb_sym. apply (eqb_neq k k') in H2. rewrite H2. apply IHkvs. apply H3.
    - destruct a as [k' v']. destruct (k' =? k) eqn:E.
      + apply eqb_eq in E. inversion H1. subst. apply Here.
      + apply There.
        * rewrite eqb_sym in E. apply eqb_neq in E. apply E.
        * apply IHkvs in H1. apply H1.
Qed.

Lemma Lookup_functional : forall A B (k : A) (v v' : B) kvs,  Lookup k v kvs -> Lookup k v' kvs -> v = v'.
Proof.
  induction kvs; intros; inversion H.
    - subst. inversion H0.
      + reflexivity.
      + exfalso. apply H3. reflexivity.
    - subst. inversion H0.
      + apply H3 in H2. inversion H2.
      + apply IHkvs. apply H4. apply H7.
Qed.

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



(* A specialized version of In for names/strings *)
Inductive NameIn (x : string) : list string -> Prop :=
  | NI_Here  : forall {xs}, NameIn x (x :: xs)
  | NI_There : forall {x' xs}, x <> x' -> NameIn x xs -> NameIn x (x' :: xs).

Lemma NameIn_In_string_equal : forall xs x, NameIn x xs <-> @In string x xs.
Proof with auto using NameIn.
  induction xs; split; intros; simpl; inversion H; subst...
    - apply IHxs in H3...
    - destruct (string_dec x a); subst...
      apply NI_There... 
      apply IHxs...
Qed.
