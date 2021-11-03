Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Theorem preservation : forall Delta T K Tn,
    Delta |-* T : K ->
    normalise T Tn ->
    Delta |-* Tn : K.
Proof. Admitted.