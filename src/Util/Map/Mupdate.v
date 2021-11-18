Require Import PlutusCert.Util.Map.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Fixpoint mupdate {X:Type} (m : partial_map X) (xts : list (string * X)) :=
  match xts with
  | nil => m
  | ((x, v) :: xts') => x |-> v ; (mupdate m xts')
  end.

Lemma mupdate_eq_cong : forall {X : Type} (m : @partial_map X) m' xts x,
    m x = m' x ->
    mupdate m xts x = mupdate m' xts x.
Proof.
  induction xts.
  - intros. assumption.
  - intros. simpl.
    destruct a.
    destruct (x =? s) eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_eq.
      rewrite update_eq.
      auto.
    + apply eqb_neq in Heqb.
      rewrite update_neq; auto.
      rewrite update_neq; auto.
Qed.

Lemma mupdate_app: forall {X : Type} (m : partial_map X) (l l' : list (string * X)),
    mupdate m (l ++ l') = mupdate (mupdate m l') l.
Proof.
  induction l; intros.
  - reflexivity.
  - destruct a. simpl. f_equal. auto.
Qed.

Lemma mupdate_shadow : forall {X : Type} (xts : list (string * X)) (m : partial_map X) x v w,
    (x |-> w; mupdate (x |-> v; m) xts) = (x |-> w; mupdate m xts).
Proof with eauto.
  induction xts. all: intros.
  - simpl. apply update_shadow.
  - simpl. 
    destruct a as [y z].
    destruct (x =? y)%string eqn:Heqb.
    + apply eqb_eq in Heqb as Heq.
      subst.
      rewrite update_shadow.
      rewrite update_shadow.
      eauto.
    + apply eqb_neq in Heqb as Hneq.
      replace (x |-> w; y |-> z; mupdate (x |-> v; m) xts) with
        (y |-> z; x |-> w; mupdate (x |-> v; m) xts) by eauto using update_permute.
      replace (x |-> w; y |-> z; mupdate m xts) with
        (y |-> z; x |-> w; mupdate m xts) by eauto using update_permute.
      f_equal...
Qed.

Lemma mupdate_shadow_In : forall {X : Type} (xts : list (string * X)) (m : partial_map X) x v,
    In x (map fst xts) ->
    mupdate (x |-> v ; m) xts = mupdate m xts.
Proof with eauto.
  induction xts. all: intros.
  - inversion H.
  - simpl.
    simpl in H.
    destruct a as [y w].
    destruct H.
    + simpl in H.
      subst.
      apply mupdate_shadow.
    + f_equal...
Qed.

Lemma mupdate_permute_In : forall {X : Type} (xts : list (string * X)) (m : partial_map X) x v,
    ~ In x (map fst xts) ->
    mupdate (x |-> v; m) xts = (x |-> v; mupdate m xts).
Proof with eauto.
  induction xts. all: intros.
  - reflexivity.
  - simpl.
    simpl in H.
    destruct a as [y w].
    destruct (x =? y)%string eqn:Heqb.
    + apply eqb_eq in Heqb.
      subst.
      exfalso...
    + apply eqb_neq in Heqb.
      rewrite update_permute...
      f_equal.
      apply IHxts.
      intros Hcon.
      apply H.
      right...
Qed.
    
Lemma inclusion_mupdate : forall {X : Type} (m m' : partial_map X) xts,
  inclusion m m' ->
  inclusion (mupdate m xts) (mupdate m' xts).
Proof.
  induction xts.
  - intros. assumption.
  - intros. simpl.
    destruct a.
    apply inclusion_update.
    auto.
Qed.

