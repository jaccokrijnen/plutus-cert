Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.

Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    (X |-> L; Delta) |-* T : K ->
    empty |-* U : L ->
    Delta |-* (substituteTCA X U T) : K.
Proof. Admitted.


Theorem substituteTCA'_preserves_kinding : forall T T' Delta X K U L,
  (X |-> L; Delta) |-* T : K ->
  empty |-* U : L ->
  substituteTCA' X U T T' ->
  Delta |-* T' : K.
Proof.
  intros T T' Delta X K U L Hkind Hkind' Hstca__T'.
  generalize dependent L.
  generalize dependent U.
  generalize dependent K.
  generalize dependent X.
  generalize dependent Delta.
  generalize dependent T'.

  induction T.
  - (* Ty_Var *)
    intros.
    rename t into Y.
    inversion Hkind. subst.
    inversion Hstca__T'.
    + (* STCA_TyVar1 *)
      subst.
      apply weakening_empty__has_kind.
      rewrite update_eq in H1.
      inversion H1.
      subst.
      apply Hkind'.
    + (* STCA_TyVar2 *)
      subst.
      rewrite update_neq in H1; auto.
      auto with typing.
  - (* Ty_Fun *)
    intros.
    inversion Hkind. subst.
    inversion Hstca__T'. subst.
    eauto with typing.
  - (* Ty_IFix *)
    intros.
    inversion Hkind. subst.
    inversion Hstca__T'. subst.
    simpl.
    eauto with typing.
  - (* Ty_Forall *)
    intros.
    rename b into bX.
    inversion Hkind. subst.
    inversion Hstca__T'. subst.
    + (* STCA_TyForall1 *)
      subst.
      apply K_Forall.
      rewrite update_shadow in H4.
      assumption.
    + (* STCA_TyForall2 *)
      subst.
      apply K_Forall.
      apply skip. (* TODO *)
    + (* STCA_TyForall3 *)
      apply K_Forall.
      eapply IHT; eauto.
      rewrite update_permute.
      assumption.
      auto.
  - (* Ty_Builtin *)
    intros.
    inversion Hkind. subst.
    inversion Hstca__T'. subst.
    simpl.
    apply K_Builtin.
    reflexivity.
  - (* Ty_Lam *)  
    intros.
    inversion Hkind. subst.
    rename b into bX.
    simpl.
    inversion Hstca__T'.
    + (* STCA_TyLam1 *)
      subst.
      apply K_Lam.
      rewrite update_shadow in H4.
      assumption.
    + (* STCA_TyLam2 *)
      subst.
      apply K_Lam.
      apply skip.
    + (* STCA_TyLam3 *)
      subst.
      apply K_Lam.
      rewrite update_permute in H4.
      eauto.
      assumption.
  - (* Ty_App *)
    intros. 
    inversion Hkind. subst.
    inversion Hstca__T'. subst.
    simpl.
    eauto with typing.
Qed.