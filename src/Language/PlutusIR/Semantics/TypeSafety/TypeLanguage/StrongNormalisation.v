Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Theorem strong_normalisation : forall T K,
    empty |-* T : K ->
    exists Tn, normalise T Tn.
Proof. 
(* ADMIT: I had no time to finish this. Should hold according to papers. *)
Admitted.