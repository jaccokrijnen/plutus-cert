From PlutusCert Require Import util.

Inductive nat :=
| O : nat
| S : nat -> nat.

Inductive le_p : nat -> nat -> Prop :=
| le_pO : forall n, le_p O n
| le_pS : forall n m, le_p n m -> le_p (S n) (S m).

Inductive le_t : nat -> nat -> Type :=
| le_tO : forall n, le_t O n
| le_tS : forall n m, le_t n m -> le_t (S n) (S m).

Fixpoint dec n m : option (le_t n m).
Proof.
    destruct n.
    - destruct m.
        + apply Some. apply le_tO.
        + apply Some. apply le_tO.
    - destruct m.
        + apply None.
        + destruct (dec n m).
            * apply Some. apply le_tS. apply l.
            * apply None.
Defined.

Lemma dec_complete : forall n m (pr : le_t n m), dec n m = Some pr -> le_t n m.
Proof.
    intros.
    destruct H.
    auto.
Qed.

Lemma dec_complete_none : forall n m, dec n m = None -> (le_p n m -> False).
Proof.
    intros n m Hdec Hle_p.
    induction Hle_p.
    all: inversion Hdec; destruct_match; auto.
Qed.

Theorem prop_to_type : forall n m, le_p n m -> le_t n m.
Proof.
    intros n m H.
    destruct (dec n m) eqn:Heq.
    - apply dec_complete in Heq. auto.
    - exfalso. apply dec_complete_none in Heq; auto.
Qed.


