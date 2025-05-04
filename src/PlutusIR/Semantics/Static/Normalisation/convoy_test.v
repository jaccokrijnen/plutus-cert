Parameter eq_bool : forall (A:Type), A -> A -> bool.

Arguments eq_bool {A} _ _.

Axiom eq_bool_correct : forall (A:Type) (x y:A),
    eq_bool x y = true -> x = y.

Axiom eq_bool_correct' : forall (A:Type) (x y:A),
     x = y -> eq_bool x y = true.

Definition test {A:Type} (x y:A) : option (x = y) :=
    match eq_bool x y as b return eq_bool x y = b -> option (x = y) with
    | true  => fun p => Some (eq_bool_correct A x y p)
    | false => fun _ => None
    end (eq_refl (eq_bool x y)).

From Coq Require Import ssreflect.

Definition eq_dec {A : Type} (n m : A) : {n = m} + {n <> m}.
  (* decide equality. *)
  admit.
Admitted.

Theorem basic (A : Type) (x y : A) (p : x = y) : test x y <> None.
Proof.
rewrite p /test.
 move: eq_refl. 
 case: {2 3}(eq_bool y y).
 - intros. discriminate.
 - by rewrite eq_bool_correct'.
Qed.