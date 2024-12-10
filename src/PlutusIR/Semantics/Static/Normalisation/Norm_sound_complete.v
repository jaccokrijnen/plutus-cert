From PlutusCert Require Import PlutusIR Normalisation.Normalisation Strong_normalisation Kinding.Kinding Type_reduction.


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

Definition normaliser T Δ K (Hwk : Δ |-* T : K) :=
  let snt := strong_normalisation Hwk in
  projT1 (SN__normalise T snt).

Theorem norm_sound T Tn Δ K (Hwk : Δ |-* T : K) :
  normaliser T Δ K Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normaliser in H.
  destruct SN__normalise in H.
  subst.
  assumption.
Qed.

Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normaliser T Δ K Hwk = Tn.
Proof.
  intros HnormR.
  unfold normaliser.
  destruct SN__normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.
