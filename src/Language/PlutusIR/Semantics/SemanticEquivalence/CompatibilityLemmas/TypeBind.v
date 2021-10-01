Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Lemma compatibility_TypeBind : forall Delta Gamma X K T,
    Delta |-* T : K ->
    LR_logically_approximate_binding Delta Gamma (TypeBind (TyVarDecl X K) T) (TypeBind (TyVarDecl X K) T).
Proof.
  intros Delta Gamma X K T Hkind__T.
  unfold LR_logically_approximate_binding.

  split; eauto with typing.
  split; eauto with typing.

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros b_msa b'_msa b_ms b'_ms.
  intros HmsA__b_msa HmsA__b'_msa Hms__b_s Hms__b'_s.

  autorewrite with RB.
Admitted.