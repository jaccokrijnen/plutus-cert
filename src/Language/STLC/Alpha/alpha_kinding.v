Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
From PlutusCert Require Import variables util Alpha.alpha STLC STLC.Kinding Util.List alpha_freshness alpha_rename.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Alpha equivalence of types *)

(* Contextual alpha equivalence: kinding contexts that match alpha contexts*)
Inductive CAlpha : list (string * string) -> list (string * PlutusIR.kind) -> list (string * PlutusIR.kind) -> Prop :=
  | calpha_nil D : CAlpha [] D D (* Non-empty kinding enviornments because id renamings are like no renamings. TODO: think whether we want to allow that or want to enforce that id renamings are in the alpha enviornment always*)
  | calpha_cons x y K sigma Gamma Gamma' :
    CAlpha sigma Gamma Gamma' ->
    CAlpha ((x, y)::sigma) ((x, K)::Gamma) ((y, K)::Gamma').
  (* | calpha_id x K sigma Gamma Gamma' :
    CAlpha sigma Gamma Gamma' ->
    CAlpha sigma ((x, K)::Gamma) ((x, K)::Gamma'). *)

Set Printing Implicit.

(* Exercise and possibly useful *)
Lemma alpha_preserves_kinding sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> STLC.Kinding.has_kind Gamma s A -> STLC.Kinding.has_kind Gamma' t A.
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
    inversion HType; subst;
    specialize (IHHAlpha ((y, A)::Gamma') ((x, A)::Gamma)
      (calpha_cons x y A sigma Gamma Gamma' HCAlpha) _ H5); constructor; auto.
  - intros Gamma' Gamma HCAlpha A HType. 
    inversion HType; subst; econstructor; eauto.
  - intros.
    inversion H; subst.
    constructor. auto.
Qed.
