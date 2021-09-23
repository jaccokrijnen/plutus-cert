Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstituteT_PreservesKinding.

Theorem beta_reduce__preserves_kinding : forall T K,
  empty |-* T : K ->
  empty |-* (beta_reduce T) : K.
Proof.
  induction T; try solve [intros; inversion H; subst; simpl; eauto with typing].
  - intros. inversion H. subst. simpl. apply K_Forall. eapply IHT. eauto with typing.
  - intros. inversion 
  induction 1. try solve [intros; inversion H; simpl; eauto with typing].
  - simpl.
    destruct (beta_reduce T1).
    all: eauto with typing.
    eapply substituteT_preserves_kinding; eauto.
    inversion IHhas_kind1; eauto.
    eapply IH
    apply IHhas_kind2.
  - (* Ty_Var *)
    intros.
    simpl.
    eauto with typing.
    rename t into Y.
    inversion Hkind. subst.
    simpl.
    destruct (X =? Y) eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply weakening_empty__has_kind.
      rewrite update_eq in H1.
      inversion H1.
      subst.
      apply Hkind'.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite update_neq in H1; auto.
      auto with typing.
  - (* Ty_Fun *)
    intros.
    inversion Hkind. subst.
    simpl.
    eauto with typing.
  - (* Ty_IFix *)
    intros.
    inversion Hkind. subst.
    simpl.
    eauto with typing.
  - (* Ty_Forall *)
    intros.
    rename b into bX.
    inversion Hkind. subst.
    simpl.
    destruct (X =? bX) eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Forall.
      rewrite update_shadow in H4.
      assumption.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Forall.
      eapply IHT; eauto.
      rewrite update_permute.
      assumption.
      auto.
  - (* Ty_Builtin *)
    intros.
    inversion Hkind. subst.
    simpl.
  - (* Ty_Lam *)  
    apply K_Builtin.
    intros.
    inversion Hkind. subst.
    rename b into bX.
    simpl.
    destruct (X =? bX) eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam.
      rewrite update_shadow in H4.
      assumption.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Lam.
      rewrite update_permute in H4.
      eauto.
      assumption.
  - (* Ty_App *)
    intros. 
    inversion Hkind. subst.
    simpl.
    eauto with typing.
Qed.