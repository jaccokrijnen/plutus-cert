Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.


Lemma msubst_TermBind : forall ss stricty x T e b',
    msubst_binding ss (TermBind stricty (VarDecl x T) e) b' ->
    exists e',
      msubst_term ss e e' /\
      b' = TermBind stricty (VarDecl x T) e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists e.
    eauto using msubst_term__nil.
  - inversion H. subst.
    rename b'0 into b''.
    inversion H2. subst.
    rename t' into e''.
    apply IHss in H5.
    destruct H5 as [e' [Hms__e' Heq]].
    subst.
    eauto using msubst_term__cons.
Qed.

Lemma msubstA_TermBind : forall ss stricty x T e b',
    msubstA_binding ss (TermBind stricty (VarDecl x T) e) b' ->
    exists e',
      msubstA ss e e' /\
      b' = TermBind stricty (VarDecl x (msubstT ss T)) e'.
Proof.
  induction ss; intros.
  - inversion H. subst.
    exists e.
    eauto using msubstA_nil.
  - inversion H. subst.
    rename b'0 into b''.
    inversion H2. subst.
    rename t' into e''.
    apply IHss in H5.
    destruct H5 as [e' [Hmsa__e' Heq]].
    subst.
    eauto using msubstA_cons.
Qed.

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
  intros Hmsa__b_msa Hmsa__b'_msa Hms__b_ms Hms__b'_ms.

  apply msubstA_TermBind in Hmsa__b_msa as temp.
  destruct temp as [t_msa [Hmsa__t_msa Heq]].
  apply msubstA_TermBind in Hmsa__b'_msa as temp.
  destruct temp as [t'_msa [Hmsa__t'_msa Heq']].
  subst.

  apply msubst_TermBind in Hms__b_ms as temp.
  destruct temp as [t_ms [Hms__t_ms Heq]].
  apply msubst_TermBind in Hms__b'_ms as temp.
  destruct temp as [t'_ms [Hmsa__t'_ms Heq']].
  subst.

  autorewrite with RB.

  split. {
    apply skip.
  }
  split. {
    apply skip.
  }

  unfold LR_logically_approximate in IH_LR.

  apply skip.
Admitted.