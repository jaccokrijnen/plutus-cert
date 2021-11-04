Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalToValue.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.Bigstep.EvalValue.

(** * [eval] is deterministic *)

(** The next Lemma seems to follow easily from inversion on the assumption and it is 
    therefore not really necessary to dedicate a Lemma to it. However, we need to  prove 
    this Lemma separately because the [inversion] tactic could not figure out this equality 
    during the [eval__deterministic] proof below. *)
Lemma compare_IfThenElse_conditions : forall T T' (t_e t_e' : Term) cond cond', 
    Apply (Apply (TyInst (Builtin IfThenElse) T) (Constant (Some (ValueOf DefaultUniBool cond)))) t_e = 
      Apply (Apply (TyInst (Builtin IfThenElse) T') (Constant (Some (ValueOf DefaultUniBool cond')))) t_e' -> 
    cond = cond'.
Proof.
  intros.
  inversion H. 
  subst.
  apply Eqdep.EqdepTheory.inj_pair2 in H2.
  subst.
  reflexivity.
Qed.

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

Ltac e :=
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

Ltac f :=
  match goal with
  | H : ~ is_error (Error ?T) |- ?P =>
      exfalso; apply H; constructor
  end.

Ltac g :=
  match goal with
  | H : neutral ?t |- ?P =>
      try solve [inversion H]
  | H : neutral_value ?n ?t |- ?P =>
      try solve [inversion H]
  end.

Ltac solf :=
  try solve [repeat (e || f || g || eauto)].

Ltac solf' :=
  repeat (e || f || g || eauto).

Ltac h n :=
  match goal with
  | H : ?t =[?j]=> ?v |- ?P =>
      inversion H; clear H; subst; 
      try solve [
        solf' || exfalso; eauto
      ];
      match n with
      | S (S ?n') => try (h (S n'))
      end
  end.

(** ** The main result *)
Theorem eval__deterministic : forall x y1 j1,
  x =[j1]=> y1 ->
  P_eval x y1 j1.
Proof with eauto.
  apply eval__ind with (P := P_eval) (P0 := P_eval_bindings_nonrec) (P1 := P_eval_bindings_rec).
  all: intros; autounfold.
  all: intros y5 j5 Hev.
  all: unfold_predicates.
  all: try solve [inversion Hev; subst; solf].
  - inversion Hev; subst. 
    all: try solve[solf].
    + inversion H10. subst.
      apply eval_value in H12.
      autounfold in H12.
      e.
      inversion H10. subst.
      inversion H15.
    + inversion H8.
      subst.
      eapply fully_applied_neutral__subsumes__neutral_value in H13...
      eapply eval_value in H13 as H14.
      autounfold in H14.
      e.
      g.
Admitted.