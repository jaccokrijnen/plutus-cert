From PlutusCert Require Import 
  PlutusIR 
  Normalization.BigStep 
  Kinding.Kinding
  Kinding.Checker
  Normalization.SmallStep
  Util
  SubstituteTCA
  SN_PIR
  Normalizer
  Normalization.Preservation
  .
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Program.Equality.

(* Dependently typed version: Normalization is sound for well-kinded types *)
Theorem norm_sound Tn {T Δ K} (Hwk : Δ |-* T : K) :
  normalizer_wk Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normalizer_wk in H.
  destruct SN_normalise in H; eauto.
  subst.
  assumption.
Qed.

(* Dependently typed version: Normalization is complete for well-kinded types *)
Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normalizer_wk Hwk = Tn.
Proof.
  intros HnormR.
  unfold normalizer_wk.
  destruct SN_normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.

From Coq Require Import ssreflect.

(* The normalizer is sound for well-kinded types*)
Theorem normalizer_sound Δ T Tn :
  normalizer Δ T = Some Tn -> normalise T Tn.
Proof.
  unfold normalizer.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TBased on https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  eapply norm_sound; eauto.
Qed.

(* The normalizer is complete for well-kinded types
*)
Theorem normalizer_complete {K Δ T Tn} :
  Δ |-* T : K -> normalise T Tn -> normalizer Δ T = Some Tn.
Proof.
  unfold normalizer.
  intros.
  apply kind_checking_complete in H.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => //.
  - intros.
    f_equal.
    eapply norm_complete; eauto.
  - intros.
    rewrite H in e.
    discriminate.
Qed.

(* Remove kinding contexts from a triple *)
Fixpoint remove_deltas  {A B C : Type} (xs : list (A * B * C)) :=
  match xs with
  | nil => nil 
  | (X, T, _) :: xs' => (X, T) :: (remove_deltas xs')
  end.

(* Remove_deltas distributes *)
Lemma remove_deltas_app {A B C : Type} (xs ys : list (A * B * C)) :
  remove_deltas (xs ++ ys) = remove_deltas xs ++ remove_deltas ys.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct a.
    destruct p.
    rewrite IHxs.
    reflexivity.
Qed.
    
(* Normalization sound for list of (X, T, Δ) triples*)
Lemma map_normalizer_sound xs xs' :
  map_normalizer xs = Some xs' -> map_normalise (remove_deltas xs) xs'.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normalizer_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    rewrite Heq.
    constructor.
    + now apply IHxs.
    + eapply normalizer_sound; eauto.
Qed.

(* map_normalizer complete for well-kinded types *)
Lemma map_normalizer_complete {xs : list (string * ty * (list (string * kind)))} {xs'} :
  map_wk xs -> map_normalise (remove_deltas xs) xs' -> map_normalizer xs = Some xs'.
Proof.
  intros.
  dependent induction H0.
  - simpl.
    assert (xs = []). {
      unfold remove_deltas in x.
      destruct xs; auto.
      fold (@remove_deltas string) in x.
      destruct p as [p0 pff].
      destruct p0 as [X T].
      inversion x.
    }
    subst.
    reflexivity.
  - simpl.
    unfold bind.
    
    inversion H.
    + subst.
      simpl in x.
      inversion x.
    + assert (T = T0). 
      {
        unfold remove_deltas in x.
        destruct xs; [inversion H4 |].
        fold (@remove_deltas string) in x. 
        destruct p as [p0 pff].
        destruct p0 as [X1 T1].
        inversion x.
        subst.
        inversion H4.
        subst.
        reflexivity.
      }
      subst.
      apply (normalizer_complete H3) in H1.
      specialize (IHmap_normalise xs0 H2).
      assert (Ts = remove_deltas xs0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        auto.
      }
      specialize (IHmap_normalise H4).
      unfold map_normalizer.
      rewrite H1.
      simpl.
      fold map_normalizer.
      rewrite IHmap_normalise.
      simpl.
      assert (X = X0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        subst.
        reflexivity.
      }
      subst.
      reflexivity.
Qed.

(* The normalizer preserves kinding *)
Theorem normalizer_preserves_kinding {Δ T Tn K } :
  Δ |-* T : K -> normalizer Δ T = Some Tn -> Δ |-* Tn : K.
Proof.
  intros.
  apply (normalizer_sound) in H0.
  apply (normalisation_preserves_kinding H) in H0; auto.
Qed.
