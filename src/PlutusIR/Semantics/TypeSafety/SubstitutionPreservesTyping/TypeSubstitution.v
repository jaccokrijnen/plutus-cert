Require Import PlutusCert.PlutusIR.
Import NamedTerm.

Require Import Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.

Require Import PlutusCert.Util.List.


Theorem substituteT_preserves_kinding : forall T Delta X K U L,
  ((X, L) :: Delta) |-* T : K ->
  [] |-* U : L ->
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
      rewrite lookup_eq in H1.
      inversion H1.
      subst...
    + (* X <> Y *)
      apply eqb_neq in Heqb as Hneq.
      rewrite lookup_neq in H1...
  - (* Ty_Forall *)
    rename b into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Forall...
      apply Kinding.weakening with (Delta := ((bX, k) :: (bX, L) :: Delta)).
      all: auto using cons_shadow.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Forall.
      eapply IHT...
      apply Kinding.weakening with (Delta := (bX, k) :: (X, L) :: Delta)...
      apply cons_permute...
  - (* Ty_Lam *)  
    rename b into bX.
    destruct (X =? bX)%string eqn:Heqb.
    + (* X = bX *)
      apply eqb_eq in Heqb as Heq.
      subst.
      apply K_Lam.
      apply Kinding.weakening with (Delta := ((bX, k) :: (bX, L) :: Delta))...
      apply cons_shadow.
    + (* X <> bX *)
      apply eqb_neq in Heqb as Hneq.
      apply K_Lam.
      assert (((X, L) :: (bX, k) ::  Delta) |-* T : K2).
      { apply Kinding.weakening with (Delta' := ((X, L) :: (bX, k) :: Delta)) in H4...
        apply cons_permute...
      }
      idtac...
Qed.
