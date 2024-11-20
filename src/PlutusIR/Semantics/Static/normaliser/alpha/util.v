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
  - intros H. split.
    + intros HP. apply H. left. assumption.
    + intros HQ. apply H. right. assumption.
  - intros [H1 H2] [HP | HQ].
    + apply H1. assumption.
    + apply H2. assumption.
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