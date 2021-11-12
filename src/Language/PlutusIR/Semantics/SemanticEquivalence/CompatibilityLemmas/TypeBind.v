Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_TypeBind : forall Delta Gamma X K Tb b b' bs bs' t t' Tn,
    Delta |-* Tb : K ->
    forall Delta_ih Gamma_ih bsGn,
      b = TypeBind (TyVarDecl X K) Tb ->
      b' = TypeBind (TyVarDecl X K) Tb ->
      Delta_ih = mupdate Delta (binds_Delta b) ->
      map_normalise (binds_Gamma b) bsGn ->
      Gamma_ih = mupdate Gamma bsGn ->
      LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (Let NonRec bs' t') Tn ->
      LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn.
Proof.
Admitted.