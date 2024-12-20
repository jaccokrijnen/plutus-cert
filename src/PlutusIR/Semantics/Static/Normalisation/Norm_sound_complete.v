From PlutusCert Require Import 
  PlutusIR 
  Normalisation.Normalisation 
  Strong_normalisation 
  Kinding.Kinding 
  Kinding.Checker
  Type_reduction
  Static.Util
  CpdtTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Lemma normalise_extend T1 T2 T3 :
  step T1 T2 -> normalise T2 T3 -> normalise T1 T3.
Proof.
  intros Hstep Hnorm.
  generalize dependent T3.
  induction Hstep; intros T3 Hnorm; try solve [inversion Hnorm; try constructor; eauto].
  eapply N_BetaReduce; eauto.
  + apply N_TyLam.
    now apply normalisation__stable'__normal.
  + now apply normalisation__stable'__normal.
Qed.

(* Wouter's suggestion: do not use explicit normalizer in soundness proof*)
Theorem SN__normalise t :
  SN t -> {t' & normalise t t'}.
Proof.
  intros HSN.
  induction HSN as [t].
  (* Suppose step_d_f t = None, then t normal, then t' = t and normalise t t *)
  assert ({t' & step t t'}) as [t' Ht_steps] by admit.
  specialize (H t' Ht_steps) as [tn normt'].
  exists tn.
  now apply normalise_extend with (T2 := t').
Admitted.


Definition normaliser {T Δ K} (Hwk : Δ |-* T : K) :=
  let snt := strong_normalisation Hwk in
  projT1 (SN__normalise T snt).

Definition normaliser_Jacco Δ T : option ty :=
  match kind_check Δ T with
  | Some K => fun Hkc =>
      Some (normaliser (kind_checking_sound Δ T K Hkc))
  | None => fun _ => None
  end eq_refl.

Fixpoint map_normaliser Δ (xs : list (string * ty)) :=
  match xs with
  | nil => Some nil
  | ((X, T) :: xs') => normaliser_Jacco Δ T >>= fun Tn => 
                     map_normaliser Δ xs' >>= fun xs'' =>
                     Some ((X, Tn) ::xs'')
  end.

Lemma map_normaliser_sound Δ xs xs' :
  map_normaliser Δ xs = Some xs' -> map_normalise xs xs'.
Proof.
Admitted.

Lemma map_normaliser_complete Δ xs xs' :
  map_normalise xs xs' -> map_normaliser Δ xs = Some xs'.
Proof.
Admitted.

Theorem norm_sound Tn {T Δ K} (Hwk : Δ |-* T : K) :
  normaliser Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normaliser in H.
  destruct SN__normalise in H.
  subst.
  assumption.
Qed.

Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normaliser Hwk = Tn.
Proof.
  intros HnormR.
  unfold normaliser.
  destruct SN__normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.

From Coq Require Import ssreflect.

Theorem normaliser_Jacco_sound Δ T Tn :
  normaliser_Jacco Δ T = Some Tn -> normalise T Tn.
Proof.
  unfold normaliser_Jacco.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TODO: I don't understand (all of) this ssreflect stuff, see https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  eapply norm_sound; eauto.
Qed.

(* We need the well-kinded assumption, otherwise counterexample:
    nil |-* TyApp (Lam bX Kind_Base "bX") (Lam bY Kind_Base "bY")

    which normalises to Lam bY Kind_Base "bY",
    but normaliser_Jacco _ T will return None

*)
Theorem normaliser_Jacco_complete {K Δ T Tn} :
  Δ |-* T : K -> normalise T Tn -> normaliser_Jacco Δ T = Some Tn.
Proof.
  unfold normaliser_Jacco.
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