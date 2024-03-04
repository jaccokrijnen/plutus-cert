Require Import Bool.

Ltac destruct_hypos := repeat (match goal with
  | H : exists a, _ |- _ => destruct H
  | H : ?x /\ ?y |- _ => destruct H
  | H : ?x && ?y = true |- _ => apply andb_prop in H
  end).

Ltac destruct_if :=
      match goal with
        | |- context[if ?X then _ else _] => destruct X eqn:H_eqb
      end.

Ltac destruct_match :=
      match goal with
      | |- context[match ?X with | _ => _ end] => destruct X eqn:?
      end.

