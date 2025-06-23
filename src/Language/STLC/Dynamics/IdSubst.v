Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

From PlutusCert Require Import 
  GU_NC 
  STLC 
  util 
  variables
  psubs.


Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x sigma , IdSubst sigma -> IdSubst ((x, tmvar x)::sigma).


Lemma id_subst__id s σ :
  (* NC s σ ->  *)
  IdSubst σ -> 
  psubs σ s = s. (* even when this capturs, it doesnt matter, since it captures something and then substiutes it for the same name*)
Proof.
  intros.
  induction s.
  - induction σ.
    + reflexivity.
    + simpl. destruct a as [x1 x2].
      inversion H; subst.
      specialize (IHσ H1).
      simpl in IHσ.
      destr_eqb_eq x1 s; auto.
  - simpl.
    f_equal.
    apply IHs.
  - simpl.
    f_equal; eauto.
  - simpl; auto.
Qed.


(* Identity substitutions: Given a typing context E, give a list of term substitutions matching this E*)
Fixpoint id_subst (E : list (string * PlutusIR.kind)) : list (string * term) :=
  match E with
  | nil => nil
  | cons (x, A) E' => cons (x, tmvar x) (id_subst E')
  end.


Lemma id_subst_is_IdSubst E :
  IdSubst (id_subst E).
Proof.
  induction E.
  - constructor.
  - simpl. destruct a. constructor. assumption.
Qed.

Lemma remove_ids_IdSubst_is_nil sigma :
  IdSubst sigma -> remove_ids sigma = nil.
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - simpl.
    destruct a as [x1 x2].
    inversion H; subst.
    rewrite IHsigma; auto.
    rewrite String.eqb_refl. auto.
Qed.

Lemma IdSubst_no_binders sigma :
  IdSubst sigma -> btv_env sigma = nil.
Proof.
  intros.
  induction sigma.
  - reflexivity.
  - simpl.
    destruct a as [x1 x2].
    inversion H; subst.
    rewrite IHsigma; auto.
Qed.

Lemma id_subst__ParSeq :
  forall (σ : list (string * term)), IdSubst σ -> ParSeq σ.
Proof.
  intros.
  induction σ.
  - constructor.
  - simpl. destruct a as [x1 x2]. constructor. 
    + apply IHσ. inversion H. assumption.
    + inversion H; subst.
      rewrite (remove_ids_IdSubst_is_nil _ H1). auto.
    + inversion H; subst.
      rewrite IdSubst_no_binders; eauto.
Qed.

Lemma no_btv_in_id_subst E :
  forall x, In x (btv_env (id_subst E)) -> False.
Proof.
  intros.
  induction E.
  - simpl in H. contradiction.
  - simpl in H. destruct a as [x1 x2].
    simpl in H.
    eapply IHE. auto.
Qed.

Lemma id_subst__nc_BU E s :
  NC s (id_subst E) -> BU (id_subst E) s.
Proof.
  intros.
  unfold BU.
  split.
  - intros. apply no_btv_in_id_subst in H0. contradiction.
  - intros. apply no_btv_in_id_subst in H0. contradiction.
Qed.

(* Hint database*)
Create HintDb id_subst_db.
Hint Resolve id_subst__nc_BU : id_subst_db.
Hint Resolve id_subst__ParSeq : id_subst_db.
Hint Resolve id_subst_is_IdSubst : id_subst_db.
Hint Resolve remove_ids_IdSubst_is_nil : id_subst_db.
Hint Resolve IdSubst_no_binders : id_subst_db.
Hint Unfold id_subst : id_subst_db.
Hint Constructors IdSubst : id_subst_db.
