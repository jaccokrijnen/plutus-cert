

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Print nat_list_ind.

Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Fixpoint length (ls : nat_list) : nat :=
    match ls with 
    | NNil => O
    | NCons l ls' => S (length ls')
    end.

Fixpoint napp (l1 l2 : nat_list) : nat_list :=
    match l1 with 
    | NNil => l2
    | NCons l ls => NCons l (napp ls l2)
    end.

Theorem nlength_napp (l1 l2 : nat_list) :
    length (napp l1 l2) = plus (length l1) (length l2).
Proof.
    induction l1.
    - simpl. reflexivity.
    - simpl.
      f_equal.
      assumption.
Qed.
