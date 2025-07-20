Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
From PlutusCert Require Import variables util Alpha.alpha STLC STLC.Kinding Util.List alpha_freshness alpha_rename.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Alpha equivalence of kinding contexts *)
Inductive CAlpha : list (string * string) -> list (string * PlutusIR.kind) -> list (string * PlutusIR.kind) -> Prop :=
  | calpha_nil D : CAlpha [] D D
  | calpha_cons x y K R Γ Γ' :
    CAlpha R Γ Γ' ->
    CAlpha ((x, y)::R) ((x, K)::Γ) ((y, K)::Γ').

Set Printing Implicit.

(* Well-kindedness is preserved under alpha equivalence *)
Lemma alpha_preserves_kinding R s t A Γ Γ' :
  Alpha R s t -> CAlpha R Γ Γ' -> STLC.Kinding.has_kind Γ s A -> STLC.Kinding.has_kind Γ' t A.
Proof.
  intros HAlpha Htype.
  generalize dependent A.
  generalize dependent Γ.
  generalize dependent Γ'.
  induction HAlpha.
  - intros Γ' Γ HCAlpha A HType.
    inversion HType.
    apply K_Var; subst...
    generalize dependent Γ.
    generalize dependent Γ'.
    induction a; subst...
    + intros.
      inversion HCAlpha; subst...
      assumption.
    + intros Γ' Γ HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      inversion Hlookup.
      simpl.
      repeat rewrite Coq.Strings.String.eqb_refl.
      reflexivity.
    + intros Γ' Γ HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      simpl.
      destruct (y =? w) eqn:yw.
      * apply String.eqb_eq in yw.
        contradiction.
      * specialize (IHa Γ'0 Γ0 H4).
        unfold lookup in Hlookup.
        destruct (x =? z) eqn:xz.
        -- apply String.eqb_eq in xz.
           contradiction.
        -- fold (lookup z Γ0) in Hlookup.
          assert (Γ0 |-* (tmvar z) : A).
          {
            apply K_Var.
            assumption.
          }
           specialize (IHa H Hlookup).
           assumption.
  - intros Γ' Γ HCAlpha A0 HType.
    inversion HType; subst;
    specialize (IHHAlpha ((y, A)::Γ') ((x, A)::Γ)
      (calpha_cons x y A R Γ Γ' HCAlpha) _ H5); constructor; auto.
  - intros Γ' Γ HCAlpha A HType.
    inversion HType; subst; econstructor; eauto.
  - intros.
    inversion H; subst.
    constructor. auto.
Qed.
