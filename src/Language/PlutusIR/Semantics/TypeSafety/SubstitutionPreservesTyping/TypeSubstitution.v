Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Theorem substituteT_preserves_kinding : forall T Delta X K U L,
  (X |-> L; Delta) |-* T : K ->
  empty |-* U : L ->
  Delta |-* (substituteT X U T) : K.
Proof.
  intros T Delta X K U L Hkind Hkind'.
  generalize dependent L.
  generalize dependent U.
  generalize dependent K.
  generalize dependent X.
  generalize dependent Delta.

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
    apply K_Builtin.
    reflexivity.
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