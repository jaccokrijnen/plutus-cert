Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

From Coq Require Import Lists.List.

Lemma compatibility_TypeBind : forall Delta Gamma X K Tb b b' bs bs' t t' Tn,
    Delta |-* Tb : K ->
    forall Delta_ih Gamma_ih bsGn,
      b = TypeBind (TyVarDecl X K) Tb ->
      b' = TypeBind (TyVarDecl X K) Tb ->
      Delta_ih = (binds_Delta b) ++ Delta  ->
      map_normalise (binds_Gamma b) bsGn ->
      Gamma_ih = bsGn ++  Gamma ->
      LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (Let NonRec bs' t') Tn ->
      LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn.
Proof.
(* ADMIT: I had no time to finish this. *)
Admitted.
