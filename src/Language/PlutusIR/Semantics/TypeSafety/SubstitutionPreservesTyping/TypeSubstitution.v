Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.



Theorem substituteT_preserves_kinding : forall T Delta X K U L,
  (X |-> L; Delta) |-* T : K ->
  empty |-* U : L ->
  Delta |-* (substituteT X U T) : K.
Proof with eauto with typing.
  induction T.
  all: intros Delta X K U L Hkind__T HHkind__U.
  all: autorewrite with substituteTCA.
  all: simpl.
  all: inversion Hkind__T; subst...
  - (* Ty_Var *)
    rename t into Y.
    destruct (X =? Y)%string eqn:Heqb.
    + (* X = Y *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply Kinding.weakening_empty.
      rewrite update_eq in H1.
      inversion H1.
      subst...
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite update_neq in H1...
  - (* Ty_Forall *)
    rename b into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Forall...
      rewrite update_shadow in H4...
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Forall.
      eapply IHT...
      rewrite update_permute...
  - (* Ty_Lam *)  
    rename b into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam.
      rewrite update_shadow in H4...
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Lam.
      rewrite update_permute in H4...
Qed.