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
Theorem norm_wouter t :
  SN5 t -> {t' & normalise t t'}.
Proof.
  intros HSN.
  induction HSN as [t].
  (* Suppose step_d_f t = None, then t normal, then normalise t t *)
  assert (Ht_steps: {t' & step_d_f t = Some t'}) by admit.
  destruct Ht_steps as [t' Ht_steps].
  specialize (H t' Ht_steps).
  destruct H as [tn normt'].
  exists tn.
  apply normalise_extend with (T2 := t').
  - now apply step_d_f_to_step_d.
  - assumption.
Admitted.

Definition normalizer7' t (snt : SN5 t) :=
  projT1 (norm_wouter t snt).

Definition normalizer7 t Δ T (Hwt : SN_STLC_named.has_type Δ t T) :=
  let snt := strong_normalization_d5 Hwt in
  normalizer7' t snt.

Theorem norm_sound_prrr t tn Δ T (Hwt : SN_STLC_named.has_type Δ t T) :
  normalizer7 t Δ T Hwt = tn -> normalise t tn.
Proof.
  intros.
  unfold normalizer7 in H.
  unfold normalizer7' in H.
  destruct norm_wouter in H.
  subst.
  assumption.
Qed.

Lemma normalise_unique t t' tn1 tn2 :
  step_d_f t = Some t' -> normalise t tn1 -> normalise t' tn2 -> tn1 = tn2.
Proof.
  intros Hstep Hnorm1 Hnorm2.

Admitted.

Lemma norm_lam7 tb x T (snt : (SN5 (tmlam x T tb))) (sntb : SN5 tb):
  @normalizer7' (tmlam x T tb) snt = tmlam x T (@normalizer7' tb sntb).
Proof.
  intros.
  generalize dependent tb.
  induction snt as [tlam]; intros sntb.
  - (* If no step, I think it is easy *)
    assert (exists tlam', step_d_f tlam = Some tlam') as [tlam' Hstep_tlam] by admit.
    specialize (H tlam' Hstep_tlam).
    specialize (H sntb).
    rewrite <- H.
    clear.
    unfold normalizer7'.
    destruct norm_wouter.
    destruct norm_wouter.
    assert (x = x0).
    {
      apply (normalise_unique tlam tlam' x x0 Hstep_tlam n n0).
    }
    subst.
    simpl.
    reflexivity.
Admitted.


(* TODO: DCopied from SubstitutionPreservesTyping/substitueTca
  In that file it is defined for PlutusIR and proof is started.
 *)
Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    SN_STLC_named.has_type ((X, L) :: Delta) T K ->
    SN_STLC_named.has_type Delta U L ->
    SN_STLC_named.has_type Delta (substituteTCA X U T) K.
Admitted.

Theorem norm_complete7 Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> @normalizer7 t Δ K Hwt = tn.
Proof.
  intros HnormR.
  generalize dependent Δ.
  generalize dependent K.
  induction HnormR; intros K' Δ Hwt; subst; auto.
  - inversion Hwt; subst. (* normalise T1 (tmlam bX K T1n), so T1 is a lambda as well. 
      What if it is an app before beta reduction?*)
    (* inversion HnormR1; subst. *)
    specialize (IHHnormR2 K1 Δ H4).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H2). (* we need something like step preserves type? K' = K1 I think*)

    specialize (IHHnormR3 K' Δ). (* The body of the lambda has just type K'*)

    assert (SN_STLC_named.has_type Δ (substituteTCA bX T2n T1n) K').
    {
      apply substituteTCA_preserves_kinding with (L := K1).
      - (* By normalizer preserves typing we have Δ ⊢* (tmlam bX K T1n) : K1 → K'
              Hence K = K1 and
              (bX, K1)::Δ ⊢* T1n : K'
      *) admit.
      - (* By normalizer preserves typing we have Δ ⊢* T2n : K1  . *)
        admit.
    }
    specialize (IHHnormR3 H).
    subst.
    (* eapply norm_subst.
    exact IHHnormR1. *)
    admit.

  - 
    inversion Hwt; subst.
    rewrite <- (IHHnormR2 K1 Δ H5).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H3).
    subst.
    admit.
    (* now apply norm_app. *)
  - (* Case step_abs *)
    inversion Hwt; subst.
    rewrite <- (IHHnormR K2 ((bX, K)::Δ) H4).
    apply norm_lam7.
  - unfold normalizer.
    destruct (strong_normalization_mysn Hwt).
    unfold normalizer'.
    (* reflexivity. *)
Admitted.



(* Used to do induction over the size of SN proofs *)
Fixpoint mysn_size {t : term} (HSN : MySN t) : nat :=
  match HSN with
  | SNI0 _ => 0
  | SNI' (existT _ t' (_, HSN')) => 1 + mysn_size HSN'
  end.

Lemma mysn_size_helper {t : term} (HSN : MySN t) :
  forall f, @mysn_size t (SNI' f) <> 0.
Proof.
  intros f.
  simpl.
  destruct f as [t' p].
  destruct p as [_ HSN'].
  intros Hcontra.
  inversion Hcontra.
Qed.

Lemma norm_lam tb x T (snt : (MySN (tmlam x T tb))) (sntb : MySN tb):
  @normalizer' (tmlam x T tb) snt = tmlam x T (@normalizer' tb sntb).
Proof.
  intros.
  remember (mysn_size snt) as n.
  generalize dependent tb.
  induction n.
  - intros tb snt sntb Hsize.
    remember snt as snt_copy.
    clear Heqsnt_copy.
    destruct snt_copy.
    + (* no step for the outer lambda, so we should also get: no step for the inner lambda *)
      induction sntb.
      * simpl.
        reflexivity.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        clear Hsize.
        inversion e.
        unfold bind in H0.
        assert (step_d_f tb = None) by destruct_match.

        rewrite Hstept' in H.
        inversion H.
    + exfalso.
      inversion Hsize.
      simpl in H0.
      destruct H0.
      assert (mysn_size (SNI' (t := tmlam x T tb) s) <> 0).
      {
        apply mysn_size_helper.
        assumption.
      }
      rewrite <- Hsize in H.
      contradiction.    
  - induction sntb.
    + intros Hsize.
      induction snt.
      * simpl. reflexivity.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        clear Hsize.
        inversion Hstept'.
        unfold bind in H0.
        assert (step_d_f tb <> None) by destruct_match.
        (* contradiction: body does not step, while lambda does *)
        contradiction.
    + destruct snt.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        inversion e.
        unfold bind in H0.
        destruct_match.
      * (* size not 0 and both step: the interesting case *) 
        
        destruct s as [tb' [Hsteptb' HSNtb'] ].
        destruct s0 as [t' [Hstept' HSNt'] ].

        simpl.
        assert (tmlam x T tb' = t').
        {
          inversion Hstept'.
          unfold bind in H0.
          destruct_match.
          inversion H0.
          inversion Hsteptb'.
          reflexivity.
        }
        subst.
        simpl.
        specialize IHn with (tb := tb') (snt := HSNt') (sntb := HSNtb').
        intros.
        inversion Heqn.
        specialize (IHn H0).
        assumption.
Qed.


(* Needs a neutrality requirement *)
Lemma norm_app t1 t2 (snt : (MySN (tmapp t1 t2))) (snt1 : MySN t1) (snt2 : MySN t2) :
  STLC_normalisation.neutral_Ty (@normalizer' t1 snt1) -> @normalizer' (tmapp t1 t2) snt = tmapp (@normalizer' t1 snt1) (@normalizer' t2 snt2).
Admitted.

(* Looks complicated, but it is really a step forward, since there is no mention of normalise anymore
  If it is too difficult, we can first try to do it with t1 already normalized fully I think.
*)
Lemma norm_subst t1 t2 T1n bX K1 (snt : (MySN (tmapp t1 t2))) (snt1 : (MySN t1)) (snt2 : (MySN t2)) 
    (snsub : (MySN (substituteTCA bX (@normalizer' t2 snt2) T1n))) :
  @normalizer' t1 snt1 = tmlam bX K1 T1n -> 
    @normalizer' (tmapp t1 t2) snt = @normalizer' (substituteTCA bX (@normalizer' t2 snt2) T1n) snsub.
Admitted.

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> @normalizer t Δ K Hwt = tn.
Proof.
  intros HnormR.
  generalize dependent Δ.
  generalize dependent K.
  induction HnormR; intros K' Δ Hwt; subst; auto.
  - inversion Hwt; subst. (* normalise T1 (tmlam bX K T1n), so T1 is a lambda as well. 
      What if it is an app before beta reduction?*)
    (* inversion HnormR1; subst. *)
    specialize (IHHnormR2 K1 Δ H4).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H2). (* we need something like step preserves type? K' = K1 I think*)

    specialize (IHHnormR3 K' Δ). (* The body of the lambda has just type K'*)

    assert (SN_STLC_named.has_type Δ (substituteTCA bX T2n T1n) K').
    {
      apply substituteTCA_preserves_kinding with (L := K1).
      - (* By normalizer preserves typing we have Δ ⊢* (tmlam bX K T1n) : K1 → K'
              Hence K = K1 and
              (bX, K1)::Δ ⊢* T1n : K'
      *) admit.
      - (* By normalizer preserves typing we have Δ ⊢* T2n : K1  . *)
        admit.
    }
    specialize (IHHnormR3 H).
    subst.
    eapply norm_subst.
    exact IHHnormR1.

  - inversion Hwt; subst.
    rewrite <- (IHHnormR2 K1 Δ H5).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H3).
    subst.
    now apply norm_app.
  - inversion Hwt; subst.
    rewrite <- (IHHnormR K2 ((bX, K)::Δ) H4).
    apply norm_lam.
  - unfold normalizer.
    destruct (strong_normalization_mysn Hwt).
    unfold normalizer'.
    reflexivity.
Admitted.

Lemma extend_normalizer t1 t2 s (Hstep : step_d_f t1 = Some t2) :
  @normalizer5' t1 (SNI5 (x := t1) s) =
  @normalizer5' t2 (s t2 Hstep).
Proof.
  induction t1;
  simpl in Hstep.
Admitted.

Theorem norm_sound''' (t tn : term) (snt : SN5 t) :
  normalise t (normalizer5' snt).
Proof.
  induction snt as [t].
  assert ({t' & step_d_f t = Some t'}) as [t' Hstep] by admit. 
  specialize (H t' Hstep).
Admitted.

(* With MySN' t we get the necessary induciton hypothesis! *)
Theorem norm_sound'' (t tn : term) (snt : SN5 t) :
  normalizer5' snt = tn -> normalise t tn.
Proof.
  intros Hnorm.
  induction snt as [t].
  (* if it does not exist, result is easy by normal is normal, so for no assume it exists*)
  assert ({t' & step_d_f t = Some t'}) as [t' Hstep] by admit. 
  assert (step_d t t') by (now apply step_d_f_to_step_d in Hstep).
  apply (normalise_extend t t' tn H0).
  
  apply (H t') with (e := Hstep).
  (* We need to show normalizer5' (SN5 t') = tn
    and we know normalizer5' (SN5 t) = tn ?
  *)
  remember ((s t' Hstep) : SN5 t') as snt'.
  subst.
  symmetry.
  exact (extend_normalizer t t' s Hstep).
Admitted.

