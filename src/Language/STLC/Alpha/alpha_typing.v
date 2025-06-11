Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
From PlutusCert Require Import variables util Alpha.alpha STLC KindingSTLC Util.List alpha_freshness alpha_rename.
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
Lemma alpha_preserves_typing sigma s t A Gamma Gamma' :
  Alpha sigma s t -> CAlpha sigma Gamma Gamma' -> KindingSTLC.has_kind Gamma s A -> KindingSTLC.has_kind Gamma' t A.
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

Lemma substituteTCA_vacuous : forall R X U T T',
    Alpha R T T' ->
    ~ In X (ftv T) ->
    Alpha R (substituteTCA X U T) T'.
Proof.
  intros.
  generalize dependent T.
  generalize dependent R.
  induction T'; intros.
  all: inversion H; subst.
  all: autorewrite with substituteTCA.
  - apply not_in_ftv_var in H0.
    rewrite <- String.eqb_neq in H0.
    now rewrite H0.
  - destr_eqb_eq X x; [now constructor|].
    assert (~ In X (ftv s1)) by now apply ftv_lam_negative in H0.
    destruct (existsb (eqb x) (ftv U)) eqn:sinU.
    + simpl.
      remember (fresh2 _ s1) as Y.
      constructor.
      eapply IHT'.
      * eapply alpha_trans_rename_left; eauto.
      * apply ftv_not_in_rename; auto.
        eapply fresh2_over_key_sigma in HeqY. symmetry. eauto.
        apply in_eq.
    + constructor; auto.
  - constructor.
    + eapply IHT'1; eauto. 
      now apply not_ftv_app_not_left in H0.
    + eapply IHT'2; eauto.
      now apply not_ftv_app_not_right in H0.
  - auto.
Qed.

Corollary substituteTCA_vacuous_specialized X U T:  
  ~ In X (ftv T) ->
  Alpha nil (substituteTCA X U T) T.
Proof.
  eapply substituteTCA_vacuous; try apply alpha_ids; auto; repeat constructor.
Qed.
