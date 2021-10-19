Require Import PlutusCert.Language.PlutusIR. 
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.CaptureAvoiding.


Lemma equiv__substituteT__substituteTCA : forall a U T T',
    closed_Ty U ->
    substituteTCA' a U T T' ->
    T' = substituteT a U T.
Proof. Admitted.