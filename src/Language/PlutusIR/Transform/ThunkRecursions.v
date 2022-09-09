From PlutusCert Require Import
  Language.PlutusIR
  .
Import NamedTerm.


Polymorphic Inductive ThunkRecursions : Term -> Term -> Type := .


(*
All recursive definitions that are not of function type are thunked: this is a hack to make it compatible with fixpoint combinator
  , which requires a function type. Examples:
    - a polymorphic function like map
    - a recursive Int: x :: Int = x + x
        (Hmm, a strict binding here should not terminate, does the compiler consider this case?
         It seems like I can't generate a strict binding of non-function type that diverges:
         plutus generates nonstrict lets for expressions that are not values (it seems?))
         If only values result in strict let bindings, what is the point of having strict bindings?
    - a polymorphic value like x :: forall a. [[a]] = [] : x)
*)
