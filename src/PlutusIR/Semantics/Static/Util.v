
(* Monad maybe*)
(* Define the bind function for option type *)
Definition bind {A B : Type} (xx : option A) (f : A -> option B) : option B :=
  match xx with
  | None => None
  | Some a => f a
  end.

(* Define an infix operator for bind *)
Infix ">>=" := bind (at level 50, left associativity).
