Require Import PlutusCert.PlutusIR.

Require Export PlutusCert.Util.Map.
Require Export PlutusCert.Util.Map.Mupdate.

(** Kind and type contexts*)
Definition Delta : Type := partial_map kind.
Definition Gamma : Type := partial_map ty.
