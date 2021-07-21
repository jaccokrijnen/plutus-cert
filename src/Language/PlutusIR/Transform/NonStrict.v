From PlutusCert Require Import
  Language.PlutusIR
  .

(* Simulate non-strict bindings as strict bindings
   by wrapping the term in a lambda that accepts a unit *)
Polymorphic Inductive SimNonStrict : Term -> Term -> Type := .

