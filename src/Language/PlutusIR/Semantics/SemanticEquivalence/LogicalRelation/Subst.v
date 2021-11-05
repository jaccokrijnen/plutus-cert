Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Tymapping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RC.Helpers.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RD.Helpers.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RG.Helpers.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RV.Helpers.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Util.Map.Mupdate.
Require Import PlutusCert.Util.List.

Require Import Coq.Lists.List.

Local Open Scope string_scope.



(** Properties of substitutions *)

Lemma subst_closed : forall t,
    closed t -> 
    forall x s,
      <{ [s / x] t }> = t.
Proof. Admitted.

Lemma substA_closed : forall t,
    closed t -> 
    forall X T,
      <{ [[T / X] t }> = t.
Proof. Admitted.

Lemma subst_not_afi : forall t x v,
    closed v ->
    ~(Term.appears_free_in x <{ [v / x] t }> ).
Proof. Admitted.

Lemma substA_not_afi : forall t X U,
    Ty.closed U ->
    ~(Annotation.appears_free_in X <{ [[U / X] t }> ).
Proof. Admitted.

Lemma duplicate_subst : forall x t v v',
    closed v ->
    <{ [v' / x] ([v / x] t) }> = <{ [v / x] t }>.
Proof. Admitted.

Lemma duplicate_substA : forall X t U U',
    Ty.closed U ->
    <{ [[U' / X] ([[U / X] t) }> = <{ [[U / X] t }>.
Proof. Admitted.

Lemma duplicate__subst_bnr : forall x bs v v',
    closed v ->
    <{ [v' / x][bnr] ([v / x][bnr] bs) }> = <{ [v / x][bnr] bs }>.
Proof. Admitted.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    <{ [v1/x1]([v/x]t) }> = <{ [v/x]([v1/x1]t) }>.
Proof. Admitted.

Lemma swap__subst_bnr : forall bs x x1 v v1,
    x <> x1 ->
    closed v ->
    closed v1 ->
    <{ [v1/x1][bnr]([v/x][bnr] bs) }> = <{ [v/x][bnr]([v1/x1][bnr] bs) }>.
Proof. Admitted.



(** ** Properties of multi-substitutions *)

Lemma msubst_closed : forall t,
    closed t ->
    forall ss,
       msubst_term ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite subst_closed; assumption.
Qed.

Lemma msubstA_closed : forall t,
    closed t ->
    forall ss,
      msubstA_term ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a.
    simpl.
    rewrite substA_closed; assumption.
Qed.

Lemma subst_msubst : forall env x v t,
    closed v ->
    closed_env env ->
    msubst_term env <{ [v/x]t }> = <{ [v/x] {msubst_term (drop x env) t} }>.
Proof.
  induction env; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    rewrite duplicate_subst; auto.
  - apply eqb_neq in Heqb as Hneq.
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst' : forall env x v t,
    closed v ->
    closed_env env ->
    msubst_term (drop x env) <{ [v/x]t }> = <{ [v/x] {msubst_term (drop x env) t} }>.
Proof.
  induction env; intros; auto.
  destruct a. simpl.
  inversion H0.
  destruct (s =? x) eqn:Heqb.
  - apply eqb_eq in Heqb as Heq.
    subst.
    eauto.
  - apply eqb_neq in Heqb as Hneq.
    simpl.  
    rewrite swap_subst; eauto.
Qed.

Lemma subst_msubst'' : forall env x xs v t,
    closed v ->
    closed_env env ->
    ~ In x xs ->
    msubst_term (mdrop xs env) <{ [v/x]t }> = <{ [v/x] {msubst_term (mdrop xs env) t} }>.
Proof. Admitted.

Lemma subst_bnr__msubst_bnr : forall env x v bs,
    closed v ->
    closed_env env ->
    msubst_bindings_nonrec env <{ [v/x][bnr] bs }> = <{ [v/x][bnr] {msubst_bindings_nonrec (drop x env) bs} }>.
Proof.
  induction env; intros; auto.
  destruct a. simpl.
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
    msubst_bindings_nonrec (drop x env) <{ [v/x][bnr] bs }> = <{ [v/x][bnr] {msubst_bindings_nonrec (drop x env) bs} }>.
Proof. Admitted.

Lemma substA_msubstA : forall envA X U t,
    Ty.closed U ->
    msubstA_term envA <{ [[U/X]t }> = <{ [[U/X] {msubstA_term (drop X envA) t} }>.
Proof. Admitted.

Lemma substA_msubst : forall X U env t,
    Ty.closed U ->
    <{ [[U / X] (/[ env /] t ) }> =  <{ /[ env /] ([[U / X] t) }> .
Proof. Admitted.

(** ** Properties of multi-extensions *)

Lemma mupdate_lookup : forall (c : tass) (x : name),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    destruct a.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_eq.
      reflexivity.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_neq; auto.
Qed.

Lemma mupdate_drop : forall (c : tass) x T,
    (x |-> T; mupdate empty c) = (x |-> T; mupdate empty (drop x c)).
Proof. 
  induction c; intros. 
  - auto.
  - destruct a.
    simpl.
    destruct (s =? x) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_shadow.
      auto.
    + apply eqb_neq in Heqb as Hneq.
      rewrite update_permute; auto.
      simpl.
      assert ((x |-> T; s |-> t; mupdate empty (drop x c)) = (s |-> t; x |-> T; mupdate empty (drop x c))). {
        apply update_permute. auto. 
      }
      rewrite H.
      f_equal.
      auto.
Qed.

(*
Lemma mupdate_drop : forall (c : tass) Gamma x x',
      lookupT (mupdate Gamma (drop x c)) x' 
    = if String.eqb x x' 
        then lookupT Gamma x' 
        else lookupT (mupdate Gamma c) x'.
Proof. Admitted.
*)

Lemma mupdate_unfold : forall {X : Type} (c : list (string * X)) x (v : X),
    (x |-> v; mupdate empty c) = mupdate empty ((x, v) :: c).
Proof. intros. auto. Qed.

Lemma mdrop_nil : forall X ns,
    @mdrop X ns nil = nil.
Proof. induction ns; auto. Qed.

(** ** Properties of Instantiations *)

(** ** Congruence lemmas on [eval] *)

(** ** Multi-substitutions preserve typing *)

Fixpoint mgsubst (xts : tass) (Gamma : Gamma) : Context.Gamma :=
  match xts with
  | nil => Gamma
  | ((a, T) :: xts') => mgsubst xts' (gsubst a T Gamma)
  end.



Lemma mgsubst_nil : forall Gamma,
    mgsubst nil Gamma = Gamma.
Proof. intros. apply Coq.Logic.FunctionalExtensionality.functional_extensionality. intros. unfold mgsubst. destruct (Gamma x); auto. Qed.

Lemma mgsubst_absorbs_msubstT : forall xts x T Gamma,
    mgsubst xts (x |-> T; Gamma) = (x |-> msubstT xts T; mgsubst xts Gamma).
Proof.
  induction xts.
  - auto.
  - intros.
    destruct a. 
    simpl.
    rewrite <- gsubst_absorbs_substituteT.
    eauto.
Qed.

Lemma mgsubst_empty : forall xts,
    mgsubst xts empty = empty.
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
      mupdate Delta ck ,, Gamma |-+ t : T ->
      normalise (msubstT (msyn1 rho) T) Tn ->
      Delta ,, mgsubst (msyn1 rho) Gamma |-+ (msubstA_term (msyn1 rho) t) : Tn. 
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
    + eapply substituteA_preserves_typing.
      * eauto.
      * eauto.
      * apply Hn1.
    + eassumption. 
Qed.

Lemma msubstA_preserves_typing_2 : forall rho ck,
    RD ck rho ->
    forall Delta Gamma t T Tn,
      mupdate Delta ck ,, Gamma |-+ t : T ->
      normalise (msubstT (msyn2 rho) T) Tn ->
      Delta ,, mgsubst (msyn2 rho) Gamma |-+ (msubstA_term (msyn2 rho) t) : Tn. 
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
    + eapply substituteA_preserves_typing.
      * eauto.
      * eauto.
      * apply Hn1.
    + eassumption. 
Qed.

Lemma msubst_preserves_typing_1 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      empty ,, (mgsubst (msyn1 rho) (mupdate Gamma c)) |-+ t : T ->
      empty ,, (mgsubst (msyn1 rho) Gamma) |-+ (msubst_term e1 t) : T. 
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V.
  - intros.
    simpl.
    assumption.
  - intros.
    eapply RV_typable_empty_1 in H as temp; eauto.
    destruct temp as [Tn'[Hnorm__Tn Htyp__v1]].
    eapply IHV; eauto.
    eapply substitution_preserves_typing.
    + simpl in H1.
      rewrite mgsubst_absorbs_msubstT in H1.
      eauto.
    + eauto.
    + eauto.
Qed.

Lemma msubst_preserves_typing_2 : forall rho k c e1 e2,
    RG rho k c e1 e2 ->
    0 < k ->
    forall Gamma T t,
      empty ,, (mgsubst (msyn2 rho) (mupdate Gamma c)) |-+ t : T ->
      empty ,, (mgsubst (msyn2 rho) Gamma) |-+ (msubst_term e2 t) : T. 
Proof.
  intros rho k c e1 e2 V Hlt.
  induction V.
  - intros.
    simpl.
    assumption.
  - intros.
    eapply RV_typable_empty_2 in H as temp; eauto.
    destruct temp as [Tn [Hnorm__Tn Htyp__v2]].
    eapply IHV; eauto.
    eapply substitution_preserves_typing.
    + simpl in H1.
      rewrite mgsubst_absorbs_msubstT in H1.
      eauto.
    + eauto.
    + eauto.
Qed. 

Lemma msubstT_preserves_kinding_1 : forall ck rho,
  RD ck rho ->
  forall Delta T K,
    (mupdate Delta ck) |-* T : K ->
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
    (mupdate Delta ck) |-* T : K ->
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