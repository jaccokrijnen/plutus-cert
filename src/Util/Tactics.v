Ltac destruct_hypos := repeat (match goal with
  | H : exists a, _ |- _ => destruct H
  | H : ?x /\ ?y |- _ => destruct H
  end).
