Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Util.Map.
Require Export PlutusCert.Util.Map.Mupdate.

(** Kind and type contexts*)
Definition Delta : Type := partial_map Kind.
Definition Gamma : Type := partial_map Ty.
