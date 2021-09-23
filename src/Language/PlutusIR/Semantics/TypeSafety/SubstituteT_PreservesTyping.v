Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Theorem substituteT_preserves_kinding : forall T ctx X K T' K',
  (X |K-> K' ; ctx) |-* T : K ->
  (forall Gamma, (empty, Gamma) |-* T' : K') ->
  ctx |-* (substituteT X T' T) : K.
Proof.
  intros T ctx X K T' K' Hkind Hkind'.
  generalize dependent ctx.
  generalize dependent T'.
  generalize dependent K'.
  generalize dependent X.
  generalize dependent K.
  induction T.
  - (* Ty_Var *)
    intros.
    rename t into Y.
    inversion Hkind. subst.
    simpl.
    destruct (X =? Y) eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      destruct ctx as [Delta Gamma].
      apply weakening__has_kind with (empty, Gamma).
      * split.
        -- apply inclusion_empty.
        -- apply inclusion_refl.
      * rewrite lookupK_eq in H1.
        inversion H1.
        subst.
        apply Hkind'.
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookupK_neq in H1; auto.
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
      rewrite extendK_shadow in H4.
      assumption.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Forall.
      eapply IHT; eauto.
      rewrite extendK_permute.
      assumption.
      auto.
  - (* Ty_Builtin *)
    intros.
    inversion Hkind. subst.
    simpl.
    apply K_Builtin.
  - (* Ty_Lam *)  
    intros.
    inversion Hkind. subst.
    rename b into bX.
    simpl.
    destruct (X =? bX) eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam.
      rewrite extendK_shadow in H4.
      assumption.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Lam.
      rewrite extendK_permute in H4.
      eauto.
      assumption.
  - (* Ty_App *)
    intros. 
    inversion Hkind. subst.
    simpl.
    eauto with typing.
Qed.