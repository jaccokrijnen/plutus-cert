Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_LetRec : forall Delta Gamma bs t bs' t' T,
    LR_logically_approximate Delta Gamma (Let Rec bs t) (Let Rec bs' t') T.
Proof with eauto_LR. Admitted.