Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Lemma compatibility_TypeBind : forall Delta Gamma X K T,
    Delta |-* T : K ->
    LR_logically_approximate_binding Delta Gamma (TypeBind (TyVarDecl X K) T) (TypeBind (TyVarDecl X K) T).
Proof with eauto_LR.
  intros Delta Gamma X K T Hkind__T.
  unfold LR_logically_approximate_binding.

  split...
Qed.