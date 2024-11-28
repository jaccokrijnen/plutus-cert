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

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K) :
    normalise t tn -> normalizer Hwt = tn.
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
      admit.
    - unfold normalizer.
      inversion Hwt; subst.
      (* unfold normalizer''. *)
      simpl.
      remember Hwt as Hwt'; clear HeqHwt'.
      assert (SN (tmvar X)).
      {
        apply strong_normalization in Hwt'.
        
        apply Hwt'.
      }
      admit.
      
      
      
Admitted.

Theorem norm_sound Δ T (t tn : term) (Hwt : SN_STLC_named.has_type Δ t T) :
    normalizer Hwt = tn -> normalise t tn.
Proof.
Admitted.