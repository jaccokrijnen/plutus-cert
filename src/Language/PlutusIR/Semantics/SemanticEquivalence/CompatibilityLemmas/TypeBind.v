Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Import Lists.List.
Import ListNotations.

Lemma compatibility_TypeBind : forall Δ Γ X K Tb b b' bs bs' t t' Tn,
    Δ |-* Tb : K ->
    forall Δ_ih Γ_ih bsGn,
      b = TypeBind (TyVarDecl X K) Tb ->
      b' = TypeBind (TyVarDecl X K) Tb ->
      Δ_ih = (binds_Delta b) ++ Δ  ->
      map_normalise (binds_Gamma b) bsGn ->
      Γ_ih = bsGn ++  Γ ->
      LR_logically_approximate Δ_ih Γ_ih (Let NonRec bs t) (Let NonRec bs' t') Tn ->
      LR_logically_approximate Δ Γ (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn.
Proof.
(* ADMIT: I had no time to finish this. *)
Admitted.
