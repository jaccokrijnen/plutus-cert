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


Require Import Lists.List.

(** WKS = Well-Kinded Substitution *)
Inductive WKS : list (name * Kind) -> list (name * Ty) -> Prop :=
  | WKS_nil :
      WKS nil nil
  | WKS_cons : forall Δ rho T X K,
      empty |-* T : K ->
      WKS Δ rho ->
      WKS ((X, K) :: Δ) ((X, T) :: rho).


Require Import Coq.Program.Equality.

Theorem msubstT_preserves_kinding T pm_Δ Δ δ K :
  WKS Δ δ ->
  pm_Δ = mupdate empty Δ ->
  pm_Δ |-* T : K ->
  empty |-* (msubstT δ T) : K.
Proof.
  intros H_WKS H_eq_Δ H_ty_T.
  generalize dependent T.
  generalize dependent pm_Δ.
  dependent induction H_WKS.
  + intros pm_Δ H_Δ T H_ty.
    subst.
    assumption.
  + intros pm_Δ H_Δ T0 H_ty_T0.
    subst.
    simpl.
    assert (H_preserve_step : (mupdate empty Δ |-* (substituteT X T T0) : K)).
    { eapply substituteT_preserves_kinding with (L := K0). 
      all: assumption.
    }
    specialize IHH_WKS with (pm_Δ := mupdate empty Δ).
    specialize (IHH_WKS eq_refl _ H_preserve_step).
    assumption.
Qed.
