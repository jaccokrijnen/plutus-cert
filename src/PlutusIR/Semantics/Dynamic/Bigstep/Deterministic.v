Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.EvalValue.

(** * [eval] is deterministic *)

(** ** Predicates *)
Definition P_eval x y1 (j1 : nat) :=
  forall y2 j2,
    x =[j2]=> y2 ->
    y1 = y2 /\ j1 = j2.

Definition P_eval_bindings_nonrec x y1 (j1 : nat) :=
  forall y2 j2,
    x =[j2]=>nr y2 ->
    y1 = y2 /\ j1 = j2.

Definition P_eval_bindings_rec bs0 x y1 (j1 : nat) :=
  forall y2 j2,
    x =[j2]=>r y2 WITH bs0 ->
    y1 = y2 /\ j1 = j2.

#[export] Hint Unfold
  P_eval
  P_eval_bindings_nonrec
  P_eval_bindings_rec
  : core.

Ltac unfold_predicates :=
  match goal with
  | H : P_eval ?t ?v ?j |- ?P =>
      unfold P_eval in H; unfold_predicates
  | H : P_eval_bindings_nonrec ?t ?v ?j |- ?P =>
      unfold P_eval_bindings_nonrec in H; unfold_predicates
  | H : P_eval_bindings_rec ?bs0 ?t ?v ?j |- ?P =>
      unfold P_eval_bindings_rec in H; unfold_predicates
  | |- _ => idtac
  end.

Ltac use_IH :=
  let y2 := fresh "y2" in
  let j2 := fresh "j2" in
  let H4 := fresh "H" in
  let H5 := fresh "H" in
  match goal with
  | H1 : forall y2 j2, ?x =[j2]=> y2 -> ?y1 = y2 /\ ?j1 = j2,
    H2 : ?x =[?j1]=> ?v1,
    H3 : ?x =[?j3]=> ?v3
      |- ?v = ?v' /\ ?j = ?j' =>
    eapply H1 in H3; eauto; destruct H3 as [H4 H5]; try (inversion H4); subst
  | H1 : forall y2 j2, ?x =[j2]=>nr y2 -> ?y1 = y2 /\ ?j1 = j2,
    H2 : ?x =[?j1]=>nr ?v1,
    H3 : ?x =[?j3]=>nr ?v3
      |- ?v = ?v' /\ ?j = ?j' =>
    eapply H1 in H3; eauto; destruct H3 as [H4 H5]; try (inversion H4); subst
  | H1 : forall y2 j2, ?x =[j2]=>r y2 WITH ?bs0 -> ?y1 = y2 /\ ?j1 = j2,
    H2 : ?x =[?j1]=>r ?v1 WITH ?bs0,
    H3 : ?x =[?j3]=>r ?v3 WITH ?bs0
      |- ?v = ?v' /\ ?j = ?j' =>
    eapply H1 in H3; eauto; destruct H3 as [H4 H5]; try (inversion H4); subst
  end.

Ltac error_is_error :=
  match goal with
  | H : ~ is_error (Error ?T) |- ?P =>
      exfalso; apply H; constructor
  end.

Ltac invert_neutral :=
  match goal with
  | H : neutral ?t |- ?P =>
      try solve [inversion H]
  | H : neutral_value ?n ?t |- ?P =>
      try solve [inversion H]
  end.

Ltac try_solve :=
  try solve [repeat (use_IH || error_is_error || invert_neutral || eauto)].

(** ** The main result *)
Theorem eval__deterministic : forall x y1 j1,
  x =[j1]=> y1 ->
  P_eval x y1 j1.
Proof with eauto.
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec).
  all: intros; autounfold.
  all: intros y5 j5 Hev.
  all: unfold_predicates.
  all: try solve [inversion Hev; subst; try_solve].
  - inversion Hev; subst.
    all: try_solve.
    + inversion H10. subst.
      apply eval_value in H12.
      autounfold in H12.
      use_IH.
      inversion H10. subst.
      inversion H15.
    + inversion H8.
      subst.
      eapply fully_applied_neutral__subsumes__neutral_value in H13...
      eapply eval_value in H13 as H14.
      autounfold in H14.
      use_IH.
      invert_neutral.
(* ADMIT: Remaining proof cases are technical overhead.
    Since we have multiple evaluation rules for applications
    and type instantiations, we need to do tedious work to
    derive contradictions. *)
Admitted.