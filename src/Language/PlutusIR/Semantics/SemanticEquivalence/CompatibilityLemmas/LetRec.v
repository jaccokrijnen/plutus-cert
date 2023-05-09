Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_LetRec : forall Δ Γ bs t bs' t' T,
    LR_logically_approximate Δ Γ (Let Rec bs t) (Let Rec bs' t') T.
Proof with eauto_LR. 
(* ADMIT: I had no time to finish this. *)
Admitted.
