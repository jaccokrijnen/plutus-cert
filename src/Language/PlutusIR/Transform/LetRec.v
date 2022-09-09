From PlutusCert Require Import
  Language.PlutusIR
  .
Import NamedTerm.

Polymorphic Inductive LetTermsRec : Term -> Term -> Type := .

(* TODO: use fixpoint combinator. Probably tough *)
