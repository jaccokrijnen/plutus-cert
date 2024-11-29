From PlutusCert Require Import STLC_named STLC_normalisation SN_STLC_named STLC_named_typing.
Require Import Coq.Lists.List.
Import ListNotations.

(* sound: if function, then relation*)
(* complete: if relation, then function*)

(* Lemma strong_normalization_SN :
  forall E s T (H : SN_STLC_named.has_type E s T), strong_normalization H = SN s.
Proof.
  (* This requires proving equivalence, likely with the definition of `strong_normalization`. *)
Admitted. *)

Lemma uhm t t' :
  step_d_f t = t' -> True.
Proof.
  intros.
  destruct (step_d_f t) eqn:Heq.
Admitted.

Lemma x :
  normalizer'' 
Admitted.

Theorem norm_complete_mysn Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> @normalizerMySN t Δ K Hwt = tn.
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
  - admit.
  - inversion Hwt; subst.
    specialize (IHHnormR K2 ((bX, K)::Δ) H4).
    unfold normalizerMySN.
    destruct (strong_normalization_mysn Hwt).
    + unfold normalizer''.
      unfold normalizerMySN in IHHnormR.
      destruct (strong_normalization_mysn H4).
      * unfold normalizer'' in IHHnormR. subst. reflexivity.
      * (* Should yield a contradiction. 
        If step_d_f T0 = Some t', then step_d_f (tmlam bX K T0) = Some (tmlam bX K t').


        *)
        inversion e.
        unfold bind in H0.
        assert (step_d_f T0 = None) by admit.
        destruct s as [t' [HstepT0' HSNt'] ].
        rewrite HstepT0' in H.
        inversion H.      
    + destruct s as [t' [HstepT HSNt'] ]. 
      unfold normalizerMySN in IHHnormR.
      destruct (strong_normalization_mysn H4) in IHHnormR.
      * inversion HstepT.
        unfold bind in H0.
        assert (step_d_f T0 <> None) by admit. (* Follows from the match*)
        contradiction.
      * destruct s as [t'0 [HstepT0 HSNt'0] ].
        (* unfold normalizer'' in IHHnormR. *)
        unfold normalizer''.
        destruct HSNt'.
        inversion IHHnormR.
        (* assert (t' = tmlam bX K t'0) by admit. *)
        subst.
        
        f_equal.
        subst.
        admit.
        admit.
  
  - unfold normalizerMySN.
    destruct (strong_normalization_mysn Hwt).
    unfold normalizer''.
    reflexivity.

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K) :
    normalise t tn -> @normalizer t Δ K Hwt = tn.
Proof.
    intros HnormR.
    generalize dependent Δ.
    generalize dependent K.
    induction HnormR; intros K' Δ Hwt; subst; auto.
    - inversion Hwt; subst.

      (* IHHnormR2:
        K0 is the type of T2, which is K1
      *)
      specialize (IHHnormR2 K1 Δ H4).

      (* IHHnormR1 K0 is the type of T1, which is K1 -> K'*)
      specialize (IHHnormR1 (tp_arrow K1 K') Δ H2).

            (* IHHnormR3:
        K0 is the type of substituteTCA bX T2n T1n, hence it is the type of T1n
        which should have the same type as T1.
        Which is K1 -> K'.
        *)
      specialize (IHHnormR3 (tp_arrow K1 K') Δ).

      admit.
    - admit.
    - 
      (* specialize (IHHnormR ((bX, K)::Δ)). *)
      inversion Hwt; subst.
      specialize (IHHnormR K2 ((bX, K)::Δ) H4).
      unfold normalizer.
      destruct (strong_normalization_d Hwt). 
       (* simpl. *)
      unfold normalizer in IHHnormR.
      destruct (strong_normalization_d H4) in IHHnormR.
      simpl in IHHnormR.
       
      (* destruct IHHnormR. *)
      destruct (step_d_f T0) eqn:Heq.
      
      
      (*
        Suppose (step_d_f T0 = None)
        Then normalise T0 T0 and T0n = T0.

        Then also in the goal, we have that the match becomes a None, so that it becomse
        tmlam bX K T0.
      *)
       
      
      unfold step_d_f.
      
      admit.
    - unfold normalizer.
      destruct (strong_normalization_d Hwt).
      simpl.
      reflexivity.  
Admitted.

Theorem norm_sound Δ T (t tn : term) (Hwt : SN_STLC_named.has_type Δ t T) :
    normalizer Hwt = tn -> normalise t tn.
Proof.
Admitted.