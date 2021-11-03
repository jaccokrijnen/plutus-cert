Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Theorem strong_normalisation : forall T K,
    empty |-* T : K ->
    exists Tn, normalise T Tn.
Proof. Admitted.