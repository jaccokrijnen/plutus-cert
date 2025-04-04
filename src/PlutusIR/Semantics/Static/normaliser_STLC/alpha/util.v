Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
From PlutusCert Require Import STLC_named Util.List.

(* TODO: Also defined in kind checker.*)
(* Tactic to simplify proofs containing hypotheses of the form
match x with
| A => Some alpha
| B _ _ => None
end = Some beta
to conclude x = A and Some alpha = Some beta.
*)
Ltac destruct_match :=
  match goal with
  | H : (match ?X with _ => _ end = _ ) |- _ => destruct X eqn:?; try discriminate
  end.

(* Create cases for x = y and x <> y (where we move from (x =? y) = true -> x = y*)
Ltac destr_eqb_eq x y :=
  let H := fresh "H" in
  destruct (x =? y) eqn:H; [apply String.eqb_eq in H; subst | apply String.eqb_neq in H].


Lemma de_morgan2 : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  
  intros P Q. split.
  - intros H. split; auto.
  - intros [H1 H2] [HP | HQ]; auto.
Qed.

Lemma concat_not_eq_prefix (a b Y : string) :
  Y = String.append a b -> a <> "" -> Y <> b.
Proof.
  intros HY Ha.
  admit.
Admitted.

Lemma length_helper a b :
  (String.length (a ++ b)) = (String.length a + String.length b).
Proof.
Admitted.

Lemma length_concat_helper x xs :
  In x xs -> le (String.length x) (String.length (String.concat "" xs)).
Proof.
Admitted.


Lemma cons_to_append {A } (x : A) sigma :
  (x :: sigma) = (x :: nil) ++ sigma.
Proof. reflexivity. Qed.

Lemma cons_chain_to_append {A } (x y : A) sigma :
(x :: y :: sigma) = (x :: y :: nil) ++ sigma .
Proof. reflexivity. Qed.

Hint Rewrite (@cons_to_append (string * term)) (@cons_chain_to_append (string * term)) : list_simpl.

Lemma in_cons_sum {A : Type} (x y : A) (l : list A) :
  In x (y :: l) -> sum (x = y) (In x l).
Proof.
Admitted. 

(* I really do not understand universes*)
Lemma in_map_iff_sigma {A : Type} (x : string) (sigma : list (string * A)) :
  In x (map fst sigma) -> {y & In (x, y) sigma}.
Proof.
  intros.
  induction sigma.
  - inversion H.
  - destruct a.
    simpl in H.
    destr_eqb_eq s x.
    + exists a. simpl. left. auto.
    + destruct (in_dec string_dec x (map fst sigma)).
      * specialize (IHsigma i). destruct IHsigma as [y Hy].
        exists y. simpl. right. auto.
      * exfalso.
        destruct H; contradiction.
Qed.

(* Analogous to in_app_or, but for set *)
Lemma in_app_sum {A : Type} (x : A) (l1 l2 : list A) :
  In x (l1 ++ l2) -> sum (In x l1) (In x l2).
Proof.
  intros Hin.
  induction l1 as [| a l1' IH].
  - (* Case: l1 is empty *)
    simpl in Hin.
    right; assumption.
  - (* Case: l1 is non-empty *)
    apply in_cons_sum in Hin.
    destruct Hin as [Hin | Hin].
    + left. subst. apply in_eq.
    + destruct (IH Hin) as [Hin_l1 | Hin_l2].
      * left; right; assumption.
      * right; assumption.
Qed.

Lemma lookup_some_then_in y t (sigma : list (string * term)) :
  lookup y sigma = Some t -> In (y, t) sigma.
Admitted.

Lemma lookup_some_then_in_values {A : Type} y t (sigma : list (string * A)) :
  lookup y sigma = Some t -> In t (map snd sigma).
Admitted.

Lemma lookup_no_key_then_none {A : Type} X (sigma : list (string * A)) :
  ~ In X (map fst sigma) -> lookup X sigma = None.
Admitted.

Lemma lookup_none_then_no_key {A : Type} X (sigma : list (string * A)) :
  lookup X sigma = None -> ~ In X (map fst sigma).
Admitted.

(* lookup is left-aligned, there could be another y in there.*)
Lemma in_then_lookup_some_and_in {A : Type} y t (sigma : list (string * A)) :
  In (y, t) sigma -> {t' & (lookup y sigma = Some t') * In (y, t') sigma}%type.
Admitted.

Lemma lookup_app_or {A : Type} y t (R1 R2 : list (string * A)) :
  lookup y (R1 ++ R2) = Some t -> sum (lookup y R1 = Some t) (lookup y R2 = Some t).
Admitted.

Lemma lookup_app_or_extended {A : Type} y t (R1 R2 : list (string * A)) :
  lookup y (R1 ++ R2) = Some t -> sum (lookup y R1 = Some t) (prod (lookup y R1 = None) (lookup y R2 = Some t)).
Proof.
  intros Happ.
  induction R1.
  + simpl in Happ. right. split; auto.
  + destruct a as [a1 a2].
    destr_eqb_eq y a1.
    * left. simpl. rewrite String.eqb_refl. simpl in Happ. rewrite String.eqb_refl in Happ. auto.
    * simpl. rewrite <- String.eqb_neq in H. rewrite String.eqb_sym in H. rewrite H.
      eapply IHR1.
      simpl in Happ. rewrite H in Happ. auto.
Qed.

Lemma not_existsb_not_in y U' : 
  existsb (eqb y) (ftv U') = false -> ~ In y (ftv U').
Proof.
Admitted.

(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.


(* string concat util *)
Lemma string_concat_app (a b : list string) :
  String.concat "" (a ++ b) = ((String.concat "" a) ++ (String.concat "" b))%string.
Admitted.

Lemma string_concat_cons (a : string) (b : list string) :
  String.concat "" (a :: b) = (a ++ (String.concat "" b))%string.
Proof.
Admitted.

Lemma string_app_assoc (a b c : string) :
  (a ++ b ++ c)%string = ((a ++ b) ++ c)%string.
Admitted.


Fixpoint lookup_r {X:Type} (k : string) (l : list (X * string)) : option X :=
  match l with
  | nil => None
  | (x, j) :: l' => if j =? k then Datatypes.Some x else lookup_r k l'
  end.


Lemma lookup_cons_helper (R : list (string * string)) s s' x y :
  lookup s ((x, y)::R) = Some s' -> x <> s -> lookup s R = Some s'.
Admitted.

Lemma lookup_r_cons_helper (R : list (string * string)) s s' x y :
  lookup_r s' ((x, y)::R) = Some s -> y <> s' -> lookup_r s' R = Some s.
Admitted.

Lemma lookup_r__app {A :Type} (k : string ) (v : A) (l1 l2 : list (A * string)) :
  lookup_r k l1 = Some v -> lookup_r k (l1 ++ l2) = Some v.
Proof.
Admitted.

(* NOT DIFFICULT: It must exist *)
Lemma lookup_split_app_helper R1 R2 s s' :
  lookup s (R1 ++ R2) = Some s' -> lookup_r s' (R1 ++ R2) = Some s ->
  ((lookup s R1 = Some s') * (lookup_r s' R1 = Some s)) +
  ((lookup s R1 = None) * (lookup_r s' R1 = None) * (lookup s R2 = Some s') * (lookup_r s' R2 = Some s)).
Proof.
  intros.
  induction R1; auto.
  destruct a.
  simpl in H.
  destr_eqb_eq s0 s.
  + inversion H; subst.
    simpl in H0.
    rewrite String.eqb_refl in H0.
    inversion H0; subst.
    left. intuition.
    * simpl. rewrite String.eqb_refl. auto.
    * simpl. rewrite String.eqb_refl. auto.
  + assert (s' <> s1).
    {
      intros Hcontra.
      subst.
      simpl in H0.
      rewrite String.eqb_refl in H0.
      inversion H0; subst.
      contradiction.
    }
    simpl in H0.
    rewrite <- String.eqb_neq in H2.
    rewrite String.eqb_sym in H2.
    rewrite H2 in H0.
    rewrite <- String.eqb_neq in H1.
    destruct (IHR1 H H0) as [ [IHR11 IHR12] | [[ [IHR21 IHR22] IHR23 ] IHR24] ].
    * left.
      simpl.
      rewrite H2.
      rewrite H1.
      auto.
    * right.
      repeat split; auto.
      -- simpl.
          rewrite H1. auto.
      -- simpl.
          rewrite H2; auto.
Qed.

(* NOT DIFFICULT *)
Lemma lookup_app_none_helper (R1 R2 : list (string * string)) s :
  lookup s (R1 ++ R2) = None -> ((lookup s R1 = None) * (lookup s R2 = None))%type.
Proof.
Admitted.

(* NOT DIFFICULT *)
Lemma lookup_r_app_none_helper (R1 R2 : list (string * string)) s :
  lookup_r s (R1 ++ R2) = None -> ((lookup_r s R1 = None) * (lookup_r s R2 = None))%type.
Admitted.

(* NOT DIFFICULT *)
Lemma lookup_some_extend_helper R1 R2 s s' :
  ((lookup s R1 = Some s') * (lookup_r s' R1 = Some s)) -> 
  ((lookup s (R1 ++ R2) = Some s') * (lookup_r s' (R1 ++ R2) = Some s))%type.
Proof.
Admitted.

Lemma lookup_none_extend_helper {R1 R2 s} :
  (lookup s R1 = None) -> (lookup_r s R1 = None) -> 
    (lookup s (R1 ++ R2) = lookup s R2 ) * (lookup_r s (R1 ++ R2) = lookup_r s R2)%type.
Proof.
Admitted.

Inductive star {A : Type} {e : A -> A -> Type } (x : A) : A -> Type :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.