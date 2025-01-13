From PlutusCert Require Import STLC_named STLC_normalisation SN_STLC_named STLC_named_typing util.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.

Lemma normalise_extend T1 T2 T3 :
  step_d T1 T2 -> normalise T2 T3 -> normalise T1 T3.
Proof.
  intros Hstep Hnorm.
  generalize dependent T3.
  induction Hstep; intros T3 Hnorm; try solve [inversion Hnorm; try constructor; eauto].
  eapply N_BetaReduce; eauto.
  + apply N_TyLam.
    admit (* Follows from normalisation__stable'__normal *).
  + admit.  (* Follows from normalisation__stable'__normal *)
Admitted.

(* Wouter's suggestion: do not use explicit normalizer in soundness proof*)
Theorem SN_d__normalise t :
  SN_d t -> {t' & normalise t t'}.
Proof.
  intros HSN.
  induction HSN as [t].
  (* Suppose step_d_f t = None, then t normal, then t' = t and normalise t t *)
  assert ({t' & step_d t t'}) as [t' Ht_steps] by admit.
  specialize (H t' Ht_steps) as [tn normt'].
  exists tn.
  now apply normalise_extend with (T2 := t').
Admitted.

Definition normaliser t Δ T (Hwt : SN_STLC_named.has_type Δ t T) :=
  let snt := strong_normalization_d Hwt in
  projT1 (SN_d__normalise t snt).

Theorem norm_sound t tn Δ T (Hwt : SN_STLC_named.has_type Δ t T) :
  normaliser t Δ T Hwt = tn -> normalise t tn.
Proof.
  intros.
  unfold normaliser in H.
  destruct SN_d__normalise in H.
  subst.
  assumption.
Qed.

(* see normalisation__deterministic in Normalisation.v*)
Lemma normalise_unique t tn1 tn2 :
  normalise t tn1 -> normalise t tn2 -> tn1 = tn2.
Proof.
Admitted.

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> normaliser t Δ K Hwt = tn.
Proof.
  intros HnormR.
  unfold normaliser.
  destruct SN_d__normalise.
  simpl.
  now apply (normalise_unique t x tn) in n.
Qed.

(* Lemma normalise_unique_step t t' tn1 tn2 :
  step_d_f t = Some t' -> normalise t tn1 -> normalise t' tn2 -> tn1 = tn2.
Proof.
  intros Hstep Hnorm1 Hnorm2.
  assert (step_d t t') by admit.
  generalize dependent tn2.
  generalize dependent tn1.
  induction H; intros tn1 Hnorm1 tn2 Hnorm2.
  - eapply N_BetaReduce in Hnorm2; eauto. 
    + eapply (normalise_unique); eauto.
    + (* ?K = A and itis al l normal so yes *) admit.
    + (* t is normal, so yes.*) admit.
  - admit.
  - admit.
  - assert (step_d_f s1 = Some s2) by admit.
    specialize (IHstep_d H0).
    inversion Hnorm1; subst.
    inversion Hnorm2; subst.
    f_equal.
    apply IHstep_d with (tn1 := T0n) (tn2 := T0n0); eauto.
    
Admitted. *)

(* Lemma extend_normalizer7 t1 t2 s (Hstep : step_d_f t1 = Some t2) :
  @normalizer7' t1 (SNI5 (x := t1) s) =
  @normalizer7' t2 (s t2 Hstep).
Proof.
    unfold normalizer7'.
    destruct norm_wouter.
    destruct norm_wouter.
    assert (x = x0).
    {
      apply (normalise_unique_step t1 t2 x x0 Hstep n n0).
    }
    subst.
    simpl.
    reflexivity.
Qed.

Lemma norm_lam7 tb x T (snt : (SN5 (tmlam x T tb))) (sntb : SN5 tb):
  @normalizer7' (tmlam x T tb) snt = tmlam x T (@normalizer7' tb sntb).
Proof.
  intros.
  unfold normalizer7'.
  destruct norm_wouter.
  simpl.
  inversion n.
  subst.
  f_equal.
  destruct norm_wouter.
  simpl.
  now apply (normalise_unique tb T0n x0 H3) in n0.
Qed.

(* Needs a neutrality requirement *)
Lemma norm_app7 t1 t2 (snt : (SN5 (tmapp t1 t2))) (snt1 : SN5 t1) (snt2 : SN5 t2) :
  STLC_normalisation.neutral_Ty (@normalizer7' t1 snt1) -> @normalizer7' (tmapp t1 t2) snt = tmapp (@normalizer7' t1 snt1) (@normalizer7' t2 snt2).
Proof.
Admitted. *)

(* Looks complicated, but it is really a step forward, since there is no mention of normalise anymore
  If it is too difficult, we can first try to do it with t1 already normalized fully I think.
*)
(* Lemma norm_subst7 t1 t2 T1n bX K1 tn (snt : (SN5 (tmapp t1 t2))) (snt1 : (SN5 t1)) (snt2 : (SN5 t2)) 
    (snsub : (SN5 (substituteTCA bX (@normalizer7' t2 snt2) T1n))) :
  @normalizer7' t1 snt1 = tmlam bX K1 T1n -> 
    @normalizer7' (tmapp t1 t2) snt = tn
    ->
    @normalizer7' (substituteTCA bX (@normalizer7' t2 snt2) T1n) snsub = tn.
Proof.
  intros Hnorm1 Hnormapp.
  simpl.
  unfold normalizer7' in Hnormapp.
  destruct norm_wouter in Hnormapp.
  rewrite <- Hnormapp. clear Hnormapp.
  unfold normalizer7' in Hnorm1.
  destruct norm_wouter in Hnorm1.
  simpl in Hnorm1.
  simpl.
  subst.
  remember (normalizer7' t2 snt2) as prrr.
  unfold normalizer7'.
  destruct norm_wouter.
  simpl.
  eapply N_BetaReduce in n1; eauto.
  - eapply (normalise_unique (tmapp t1 t2)); eauto.
  - subst.
    unfold normalizer7'.
    destruct norm_wouter.
    simpl.
    assumption.
Qed. *)


