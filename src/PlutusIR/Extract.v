From PlutusCert Require Import
  DeadCode.DecideBool
  UniqueBinders.DecOpt.

From Coq Require Import Strings.Ascii.
From Coq Require Import Extraction.
Extraction Language Haskell.
Recursive Extraction
  dec_Term
  dec_unique
  ascii_of_nat.
