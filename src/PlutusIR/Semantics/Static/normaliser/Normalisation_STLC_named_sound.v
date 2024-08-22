From PlutusCert Require Import Normalisation_STLC_named.
From PlutusCert Require Import Normalizer_STLC_named.

(* Running normalizer on named STLC results in a value that
    satisfies the normalise relation *)

Theorem normalizer_named_sound : forall t T v H_wt,
    normalizer T t H_wt = v -> normalise t v.
Proof.
    intros t T v H_wt H.
Admitted.