Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

From PlutusCert Require Import 
  GU_NC 
  STLC 
  util 
  variables
  psubs.

(* Identity subsitutions, where the term is always a variable equal to the key *)
Inductive IdSubst : list (string * term) -> Set :=
  | id_subst_nil : IdSubst nil
  | id_subst_cons : forall x σ , IdSubst σ -> IdSubst ((x, tmvar x)::σ).

(* Identity substitutions have no effect *)
Lemma id_subst__id s σ :
  IdSubst σ -> 
  psubs σ s = s. (* No need for a no-capture premise: even when this "captures", it doesnt matter, since it captures something and then substiutes it for the same name*)
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


(* Procedure for generating an identity substitution for each name in the kinding context *)
Fixpoint id_subst (Δ : list (string * PlutusIR.kind)) : list (string * term) :=
  match Δ with
  | nil => nil
  | cons (x, A) Δ' => cons (x, tmvar x) (id_subst Δ')
  end.

(* Procedure id_subst really produces identity substitutions*)
Lemma id_subst_is_IdSubst Δ :
  IdSubst (id_subst Δ).
Proof.
  induction Δ.
  - constructor.
  - simpl. destruct a. constructor. assumption.
Qed.

(* An IdSubst only contains identity substitutions *)
Lemma remove_ids_IdSubst_is_nil σ :
  IdSubst σ -> remove_ids σ = nil.
Proof.
  intros.
  induction σ.
  - reflexivity.
  - simpl.
    destruct a as [x1 x2].
    inversion H; subst.
    rewrite IHσ; auto.
    rewrite String.eqb_refl. auto.
Qed.

(* An IdSubst has no binders (no abstraction terms)*)
Lemma IdSubst_no_binders σ :
  IdSubst σ -> btv_env σ = nil.
Proof.
  intros.
  induction σ.
  - reflexivity.
  - simpl.
    destruct a as [x1 x2].
    inversion H; subst.
    rewrite IHσ; auto.
Qed.

(* An IdSubst behaves the same when applied sequentially or parallelly*)
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

(* Helper: For any kinding context, if we generate an identity substitution from it, it does not contain any binders *)
Lemma no_btv_in_id_subst Δ :
  forall x, In x (btv_env (id_subst Δ)) -> False.
Proof.
  intros.
  induction Δ.
  - simpl in H. contradiction.
  - simpl in H. destruct a as [x1 x2].
    simpl in H.
    eapply IHΔ. auto.
Qed.

(* If an identity substitution does not cause capture, then BU: the binders in the subsitution are trivially unique and not equal to any in s*)
Lemma id_subst__nc_BU Δ s :
  NC s (id_subst Δ) -> BU (id_subst Δ) s.
Proof.
  intros.
  unfold BU.
  split.
  - intros.  apply no_btv_in_id_subst in H0. contradiction.
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
