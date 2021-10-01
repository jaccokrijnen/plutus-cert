Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Lemma compatibility_TermBind : forall Delta Gamma stricty x T t t',
    Delta |-* T : Kind_Base ->
    LR_logically_approximate Delta Gamma t t' T ->
    LR_logically_approximate_binding Delta Gamma (TermBind stricty (VarDecl x T) t) (TermBind stricty (VarDecl x T) t').
Proof.
  intros Delta Gamma stricty X T t t' Hkind__T IH_LR.
  unfold LR_logically_approximate_binding.

  split. {
    eapply W_Term.
    - apply Hkind__T. 
    - apply IH_LR.
  }
  
  split. {
    eapply W_Term.
    - apply Hkind__T.
    - apply IH_LR.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros b_msa b'_msa b_ms b'_ms.
  intros HmsA__b_msa HmsA__b'_msa Hms__b_s Hms__b'_s.

  autorewrite with RB.
Admitted.