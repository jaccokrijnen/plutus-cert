Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Lemma compatibility_LetRec : forall Delta Gamma bs t bs' t' T,
    LR_logically_approximate Delta Gamma (Let Rec bs t) (Let Rec bs' t') T.
Proof with eauto_LR. 
(* ADMIT: I had no time to finish this. *)
Admitted.
