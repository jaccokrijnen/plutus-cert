Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
From PlutusCert Require Import alpha STLC_named STLC_named_typing Util.List.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Alpha equivalence of types *)

(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * type) -> list (string * type) -> Prop :=
  | calpha_nil : CAlpha [] [] []
  | calpha_cons x y K sigma Gamma Gamma' :
    CAlpha sigma Gamma Gamma' ->
    CAlpha ((x, y)::sigma) ((x, K)::Gamma) ((y, K)::Gamma').

(* Exercise and possibly useful *)
Lemma alpha_preserves_typing sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> Gamma |-* s : A -> Gamma' |-* t : A.
Proof.
  intros HAlpha Htype.
  generalize dependent A.
  generalize dependent Gamma.
  generalize dependent Gamma'.
  induction HAlpha.
  - intros Gamma' Gamma HCAlpha A HType.
    inversion HType.
    apply K_Var; subst...
    generalize dependent Gamma.
    generalize dependent Gamma'.
    induction a; subst...
    + intros.
      inversion HCAlpha; subst...
      assumption.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      inversion Hlookup.
      simpl.
      repeat rewrite Coq.Strings.String.eqb_refl.
      reflexivity.
    + intros Gamma' Gamma HCAlpha HType Hlookup.
      inversion HCAlpha; subst...
      simpl.
      destruct (y =? w) eqn:yw.
      * apply String.eqb_eq in yw.
        contradiction.
      * specialize (IHa Gamma'0 Gamma0 H4).
        unfold lookup in Hlookup.
        destruct (x =? z) eqn:xz.
        -- apply String.eqb_eq in xz.
           contradiction.
        -- fold (lookup z Gamma0) in Hlookup.
          assert (Gamma0 |-* (tmvar z) : A).
          {
            (* Strengthening typing*)
            apply K_Var.
            assumption.
          }
           specialize (IHa H Hlookup).
           assumption.
  - intros Gamma' Gamma HCAlpha A0 HType.
    inversion HType.
    specialize (IHHAlpha ((y, A)::Gamma') ((x, A)::Gamma)
      (calpha_cons x y A sigma Gamma Gamma' HCAlpha) K2 H4).
    apply K_Lam.
    assumption.
  - intros Gamma' Gamma HCAlpha A HType. 
    inversion HType.
    specialize (IHHAlpha1 Gamma' Gamma HCAlpha (tp_arrow K1 A) H2).
    specialize (IHHAlpha2 Gamma' Gamma HCAlpha K1 H4).
    apply K_App with (K1 := K1); assumption.
Qed.