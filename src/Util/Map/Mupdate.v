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

