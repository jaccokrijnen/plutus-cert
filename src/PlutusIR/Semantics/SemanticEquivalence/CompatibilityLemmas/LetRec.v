Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_LetRec : forall Delta Gamma bs t bs' t' T,
    LR_logically_approximate Delta Gamma (Let Rec bs t) (Let Rec bs' t') T.
Proof with eauto_LR.
(* ADMIT: I had no time to finish this. *)
Admitted.