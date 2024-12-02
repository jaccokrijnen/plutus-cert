From PlutusCert Require Import STLC_named STLC_normalisation SN_STLC_named STLC_named_typing util.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.

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
  dependent induction n.
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
      * 
        
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

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> @normalizer t Δ K Hwt = tn.
Proof.
  intros HnormR.
  generalize dependent Δ.
  generalize dependent K.
  induction HnormR; intros K' Δ Hwt; subst; auto.
  - inversion Hwt; subst.
    specialize (IHHnormR2 K1 Δ H4).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H2).
    specialize (IHHnormR3 (tp_arrow K1 K') Δ).
    admit.
  - inversion Hwt; subst.
    specialize (IHHnormR2 K1 Δ H5).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H3).

    unfold normalizer.
    unfold normalizer in IHHnormR1.
    unfold normalizer in IHHnormR2.

    (* Neutral T1n*)
    subst.

    destruct (strong_normalization_mysn H3).
    + (* Case: Value $ T1*)
      simpl.
      
      destruct (strong_normalization_mysn H5).
      * (* Case Value T1 && Value T2 *)
        simpl.
        
        destruct (strong_normalization_mysn Hwt).
        -- (* Correct case: Value $ (tmapp T1 T2)*)
           simpl. reflexivity.
        -- (* Contradiction, T1 T2 no step, so app neither*)
           exfalso.
           destruct s as [t' [HstepT HSNt'] ].
           inversion HstepT.

           assert (is_normal T1 = true) by admit. (* should be clear from no step *)
           rewrite H0 in H1.
           assert (is_normal T2 = true) by admit.
           rewrite H2 in H1.
           simpl in H.
           (* From H1 it follows that T1 must be of shape tmlam,
            contradiction, because of H: T1 neutral*)
           admit.
          


      * (* Case: Value T1 && Step T2 T2n *)
        destruct (strong_normalization_mysn Hwt).
        -- (* Contradiction: T2 steps, but tmapp not*)
           exfalso.
           inversion e0.
           assert (is_normal T1 = true) by admit. 
           rewrite H0 in H1.
           assert (is_normal T2 = false) by admit.
           rewrite H2 in H1.
           unfold bind in H1.
           (* H1 now says step_d_f T2 must be None, but s says it is Some*)
           admit.
        -- (* Correct case: T2 steps and app also steps *)           
            destruct s as [t' [Hstept' HSNt'] ].
            destruct s0 as [t'' [Hstept'' HSNt''] ].
            simpl.
            simpl in HnormR2.
            simpl in HnormR1.
            (* Not sure yet how to do this. 
              Probably first get: t'' = tmapp T1 t', and then same as tmlam case
            *)
            admit.
    + (* Case: step $ T1*)
  
    admit.
  - inversion Hwt; subst.
    specialize (IHHnormR K2 ((bX, K)::Δ) H4).
    
    unfold normalizer; destruct (strong_normalization_mysn Hwt);
    unfold normalizer';
    unfold normalizer in IHHnormR; destruct (strong_normalization_mysn H4);
    unfold normalizer' in IHHnormR.
    + (* Already value*)
      subst. reflexivity.
    + exfalso. 
      (* Contradiction: lambda no step, while body does. *)
      inversion e.
      unfold bind in H0.
      destruct s as [t' [HstepT0' HSNt'] ].
      destruct_match.  
    + exfalso.
      (* Contradiction: body does not step, while lambda does *)
      destruct s as [t' [HstepT HSNt'] ]. 
      inversion HstepT.
      unfold bind in H0.
      destruct_match.
    + (* Body and whole lambda step *)
      fold normalizer'.
      destruct s as [t [Hstept HSNt] ].
      destruct s0 as [tb [Hsteptb HSNtb] ].
      fold normalizer' in IHHnormR.
      assert (t = tmlam bX K tb).
      {
        inversion Hstept.
        unfold bind in H0.
        destruct_match.
        inversion Hsteptb.
        inversion H0.
        subst.
        reflexivity.
      }
      subst.
      eapply norm_lam.
  - unfold normalizer.
    destruct (strong_normalization_mysn Hwt).
    unfold normalizer'.
    reflexivity.
Admitted.

Theorem norm_sound Δ T (t tn : term) (Hwt : SN_STLC_named.has_type Δ t T) :
    normalizer Hwt = tn -> normalise t tn.
Proof.
  intros Hnorm.
  unfold normalizer in Hnorm.

  inversion Hnorm.
  
Admitted.
