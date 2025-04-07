Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RC.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RD.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RG.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Util.Map.Mupdate.
Require Import PlutusCert.Util.List.

Import PlutusNotations.

Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

(* ADMIT: We admit many lemmas here due to time constraints. They should hold or should at least hold with
   minor adjustements to our definitions. *)

(** Properties of substitutions *)

Lemma subst_closed : forall (t : term),
    closed t ->
    forall x s,
      (x, s) ⊙ t = t.
Proof. Admitted.

Lemma substA_closed : forall (t : term),
    closed t ->
    forall X (T : ty),
      (X, T) ⊙ t = t.
Proof. Admitted.

Lemma subst_not_afi : forall (t : term) x v,
    closed v ->
    ~(Term.appears_free_in x ((x,v) ⊙ t) ).
Proof. Admitted.

Lemma substA_not_afi : forall (t : term) X U,
    Ty.closed U ->
    ~(Annotation.appears_free_in X ((X, U) ⊙ t) ).
Proof. Admitted.

Lemma duplicate_subst : forall x (t : term) v v',
    closed v ->
    (x, v') ⊙ (x, v) ⊙ t = (x, v) ⊙ t.
Proof. Admitted.

Lemma duplicate_substA : forall X (t : term) U U',
    Ty.closed U ->
    (X, U') ⊙ (X, U) ⊙ t = (X, U) ⊙ t.
Proof. Admitted.

Lemma duplicate__subst_bnr : forall x (bs : list binding) v v',
    closed v ->
    (x, v') ⊙ (x, v) ⊙ bs = (x, v) ⊙ bs.
Proof. Admitted.

Lemma swap_subst : forall (t : term) x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    (x1, v1) ⊙ (x, v) ⊙ t = (x, v) ⊙ (x1, v1) ⊙ t.
Proof. Admitted.

Lemma swap__subst_bnr : forall (bs : list binding) x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    (x1, v1) ⊙ (x, v) ⊙ bs = (x, v) ⊙ (x1, v1) ⊙ bs.
Proof. Admitted.


(* Basic simplifications *)

Lemma msubst_cons x (s t : term) γ :
  ((x, s) :: γ) ⊙ t = γ ⊙ ((x, s) ⊙ t).
Proof.
reflexivity.
Qed.


Lemma msubst_bnr_cons x (s : term) (bs : list binding) γ :
  ((x, s) :: γ) ⊙ bs = γ ⊙ ((x, s) ⊙ bs).
Proof. reflexivity. Qed.


Lemma msubstA_cons x (s : ty) (t : term) γ :
  ((x, s) :: γ) ⊙ t = γ ⊙ ((x, s) ⊙ t).
Proof.
reflexivity.
Qed.

Lemma drop_cons x s y γ :
  ((x, s) :: γ) \\ y = if x =? y then γ \\ y else (x, s) :: (γ \\ y).
Proof. reflexivity. Qed.

Create HintDb subst_simpl.
Hint Rewrite
  msubst_cons
  msubstA_cons
  drop_cons
  msubst_bnr_cons
  : subst_simpl.


(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall (ss : env),
       ss ⊙ t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    autorewrite with subst_simpl.
    rewrite subst_closed; assumption.
Qed.

Lemma msubstA_closed : forall t,
    closed t ->
    forall (ss : tass),
      ss ⊙ t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    autorewrite with subst_simpl.
    rewrite substA_closed; assumption.
Qed.

Lemma subst_msubst : forall (env : list (string * term)) (x : string) v (t : term),
    closed v ->
    closed_env env ->
    env ⊙ (x, v) ⊙ t = (x, v) ⊙ (env \\ x) ⊙ t.
Proof.
  induction env; intros; auto.
  destruct a.
  autorewrite with subst_simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    rewrite duplicate_subst; auto.
  - apply eqb_neq in Heqb as Hneq.
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst' : forall env x v (t : term),
    closed v ->
    closed_env env ->
    (env \\ x) ⊙ ((x, v) ⊙ t) = (x, v) ⊙ (env \\ x) ⊙ t.
Proof.
  induction env; intros; auto.
  destruct a.
  autorewrite with subst_simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    eauto.
  - apply eqb_neq in Heqb as Hneq.
    autorewrite with subst_simpl.
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst'' : forall env x (xs : list string) v (t : term),
    closed v ->
    closed_env env ->
    ~ In x xs ->
    (env \\ xs) ⊙ (x, v) ⊙ t = (x, v) ⊙ (env \\ xs) ⊙ t.
Proof. Admitted.

Lemma subst_bnr__msubst_bnr : forall env x v (bs : list binding),
    closed v ->
    closed_env env ->
    env ⊙ ((x, v) ⊙ bs) = (x, v) ⊙ (env \\ x) ⊙ bs.
Proof.
  induction env; intros; auto.
  destruct a. autorewrite with subst_simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    rewrite duplicate__subst_bnr; auto.
  - apply eqb_neq in Heqb as Hneq.
    rewrite swap__subst_bnr; eauto.
Qed.

Lemma subst_bnr__msubst_bnr' : forall env x v bs,
    closed v ->
    closed_env env ->
    msubst_bnr (drop x env) <{ [x := v]bnr bs }> = <{ [x := v]bnr {msubst_bnr (drop x env) bs} }>.
Proof. Admitted.

Lemma substA_msubstA : forall envA X U t,
    Ty.closed U ->
    msubstA envA <{ :[X := U]t }> = <{ :[X := U] {msubstA (drop X envA) t} }>.
Proof. Admitted.

Lemma substA_msubst : forall X U env t,
    Ty.closed U ->
    <{ :[X := U] ([ env ]* t ) }> =  <{ [ env ]* (:[X := U] t) }> .
Proof. Admitted.

(** ** Properties of multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : string),
    lookup x c = lookup x (c ++ []).
Proof with auto.
  induction c.
  - auto.
  - intros.
    simpl.
    destruct a.
    destruct (s =? x) eqn:Heqb...
Qed.

(* TODO: rename to update_drop? *)
(* TODO: use setoid in the proof? *)
Lemma mupdate_drop : forall (c : tass) x T,
    inclusion ((x , T) :: c) ((x , T) :: drop x c).
Proof with auto using inclusion_refl, cons_permute, cons_shadow, inclusion_cons.
  induction c; intros...
  destruct a.
  simpl.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    transitivity ((x, T) :: c)...
  - apply eqb_neq in Heqb as Hneq.
    transitivity ((s, t) :: (x, T) :: drop x c)...
    transitivity ((s, t) :: (x, T) :: c)...
Qed.

(*
Lemma mupdate_drop : forall (c : tass) Gamma x x',
      lookupT (mupdate Gamma (drop x c)) x'
    = if String.eqb x x'
        then lookupT Gamma x'
        else lookupT (mupdate Gamma c) x'.
Proof. Admitted.
*)


(* TODO: clean this up *)
Lemma mupdate_unfold : forall {X : Type} (c : list (string * X)) x (v : X),
    ((x, v) :: c) = ((x, v) :: c).
Proof. auto. Qed.


(** ** Properties of Instantiations *)

(** ** Congruence lemmas on [eval] *)

(** ** Multi-substitutions preserve typing *)

Fixpoint mgsubst (xts : tass) (Gamma : list (string * ty)) : list (string * ty) :=
  match xts with
  | nil => Gamma
  | ((a, T) :: xts') => mgsubst xts' (gsubst a T Gamma)
  end.



Lemma mgsubst_nil : forall Gamma,
    mgsubst nil Gamma = Gamma.
Proof. reflexivity. Qed.

Lemma mgsubst_absorbs_msubstT : forall xts x T Gamma,
    mgsubst xts ((x, T) :: Gamma) = ((x, msubstT xts T) :: mgsubst xts Gamma).
Proof.
  induction xts.
  - auto.
  - intros.
    destruct a.
    simpl.
    eauto.
Qed.

Lemma mgsubst_empty : forall xts,
    mgsubst xts [] = [].
Proof. induction xts; auto. simpl. destruct a. auto. Qed.

Lemma normalise_commutes : forall ss X U T Tn,
    normalise (msubstT ss (substituteT X U T)) Tn ->
    exists T0n,
      normalise (substituteT X U T) T0n /\
      normalise (msubstT ss T0n) Tn.
Proof. Admitted.

Lemma msubstA_preserves_typing_1 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t T Tn,
      ck ++ Delta ,, Gamma |-+ t : T ->
      normalise (msubstT (msyn1 rho) T) Tn ->
      Delta ,, mgsubst (msyn1 rho) Gamma |-+ (msubstA (msyn1 rho) t) : Tn.
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    simpl.
    simpl in H0.
    apply has_type__normal in H as H1.
    apply normalisation__stable__normal in H0; auto.
    subst.
    assumption.
  - intros.
    subst.
    simpl.
    simpl in H3.
    eapply normalise_commutes in H3 as temp.
    destruct temp as [T0n [Hn1 Hn2]].
    eapply IHV.
    + eapply substA_preserves_typing.
      * eauto.
      * eauto.
      * apply Hn1.
    + eassumption.
Qed.

Lemma msubstA_preserves_typing_2 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t T Tn,
      ck ++ Delta ,, Gamma |-+ t : T ->
      normalise (msubstT (msyn2 rho) T) Tn ->
      Delta ,, mgsubst (msyn2 rho) Gamma |-+ (msubstA (msyn2 rho) t) : Tn.
Proof.
  intros rho ck V.
  induction V.
  - intros.
    subst.
    simpl.
    simpl in H0.
    apply has_type__normal in H as H1.
    apply normalisation__stable__normal in H0; auto.
    subst.
    assumption.
  - intros.
    subst.
    simpl.
    simpl in H3.
    eapply normalise_commutes in H3 as temp.
    destruct temp as [T0n [Hn1 Hn2]].
    eapply IHV.
    + eapply substA_preserves_typing.
      * eauto.
      * eauto.
      * apply Hn1.
    + eassumption.
Qed.

Lemma msubst_preserves_typing_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      [] ,, (mgsubst (msyn1 rho) (c ++ Gamma)) |-+ t : T ->
      [] ,, (mgsubst (msyn1 rho) Gamma) |-+ (msubst e1 t) : T.
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V as [ | ? ? ? ? ? ? ? H_RV H_normal H_pure ].
  - intros.
    simpl.
    assumption.
  - intros.
    eapply RV_typable_empty_1 in H_RV as temp; eauto.
    destruct temp as [Tn'[Hnorm__Tn Htyp__v1]].
    eapply IHV; eauto.
    eapply substitution_preserves_typing.
    + simpl in H.
      rewrite mgsubst_absorbs_msubstT in H.
      eauto.
    + eauto.
    + eauto.
Qed.

Lemma msubst_preserves_typing_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      [] ,, (mgsubst (msyn2 rho) (c ++ Gamma)) |-+ t : T ->
      [] ,, (mgsubst (msyn2 rho) Gamma) |-+ (msubst e2 t) : T.
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V as [ | ? ? ? ? ? ? ? H_RV H_normal H_pure ].
  - intros.
    simpl.
    assumption.
  - intros.
    eapply RV_typable_empty_2 in H_RV as temp; eauto.
    destruct temp as [Tn [Hnorm__Tn Htyp__v2]].
    eapply IHV; eauto.
    eapply substitution_preserves_typing.
    + simpl in H.
      rewrite mgsubst_absorbs_msubstT in H.
      eauto.
    + eauto.
    + eauto.
Qed.

Lemma msubstT_preserves_kinding_1 : forall ck rho,
  RD ck rho ->
  forall Delta T K,
    (ck ++ Delta) |-* T : K ->
    Delta |-* (msubstT (msyn1 rho) T) : K.
Proof.
  intros ck rho V.
  induction V; intros.
  - assumption.
  - simpl.
    eapply IHV.
    eapply substituteT_preserves_kinding.
    + apply H2.
    + assumption.
Qed.

Lemma msubstT_preserves_kinding_2 : forall ck rho,
  RD ck rho ->
  forall Delta T K,
    (ck ++ Delta) |-* T : K ->
    Delta |-* (msubstT (msyn2 rho) T) : K.
Proof.
  intros ck rho V.
  induction V; intros.
  - assumption.
  - simpl.
    eapply IHV.
    eapply substituteT_preserves_kinding.
    + apply H2.
    + assumption.
Qed.

Corollary closing_preserves_kinding_1 : forall Delta rho T K,
  RD Delta rho ->
  Delta |-* T : K ->
  []    |-* (msubstT (msyn1 rho) T) : K.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Delta) in H0.
  eapply msubstT_preserves_kinding_1...
Qed.

Corollary closing_preserves_kinding_2 : forall Delta rho T K,
  RD Delta rho ->
  Delta |-* T : K ->
  []    |-* (msubstT (msyn2 rho) T) : K.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Delta) in H0.
  eapply msubstT_preserves_kinding_2...
Qed.

Corollary closingA_preserves_typing_1 : forall Delta Gamma rho t T Tn,
    RD Delta rho ->
    Delta ,, Gamma |-+ t : T ->
    normalise (msubstT (msyn1 rho) T) Tn ->
    [] ,, mgsubst (msyn1 rho) Gamma |-+ (msubstA (msyn1 rho) t) : Tn.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Delta) in H0.
  eapply msubstA_preserves_typing_1...
Qed.

Corollary closingA_preserves_typing_2 : forall Delta Gamma rho t T Tn,
    RD Delta rho ->
    Delta ,, Gamma |-+ t : T ->
    normalise (msubstT (msyn2 rho) T) Tn ->
    [] ,, mgsubst (msyn2 rho) Gamma |-+ (msubstA (msyn2 rho) t) : Tn.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Delta) in H0.
  eapply msubstA_preserves_typing_2...
Qed.

Corollary closing_preserves_typing_1 : forall Gamma T t rho k e1 e2,
    RG rho k Gamma e1 e2 ->
    0 < k ->
      [] ,, (mgsubst (msyn1 rho) Gamma) |-+ t : T ->
      [] ,, [] |-+ (msubst e1 t) : T.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Gamma) in H1.
  replace [] with (mgsubst (msyn1 rho) []).
  eapply msubst_preserves_typing_1...
  rewrite mgsubst_empty...
Qed.

Corollary closing_preserves_typing_2 : forall Gamma T t rho k e1 e2,
    RG rho k Gamma e1 e2 ->
    0 < k ->
      [] ,, (mgsubst (msyn2 rho) Gamma) |-+ t : T ->
      [] ,, [] |-+ (msubst e2 t) : T.
Proof with eauto.
  intros.
  rewrite <- app_nil_r with (l := Gamma) in H1.
  replace [] with (mgsubst (msyn2 rho) []).
  eapply msubst_preserves_typing_2...
  rewrite mgsubst_empty...
Qed.

