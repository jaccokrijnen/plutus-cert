Require Import Coq.Strings.String.

(* Applying substitution of type A on B *)
Class Subst (A B : Type) := {
  s : A -> B -> B
}.

(* Dropping variables from substitutions *)
Class Drop (A B : Type) := {
  d : A -> list (string * B) -> list (string * B)
}.

Notation "γ ⊙ t" := (s γ t) (at level 55, right associativity).
Notation "γ \\ b" := (d b γ) (at level 50, left associativity).
