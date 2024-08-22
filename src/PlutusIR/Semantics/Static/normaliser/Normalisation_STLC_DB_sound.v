From PlutusCert Require Import Normalisation_STLC_DB.
From PlutusCert Require Import Normalizer_STLC_DB.
From PlutusCert Require Import STLC_DB_typing.
From PlutusCert Require Import SN_STLC_DB_nd.

Require Import Coq.Lists.List.
Import ListNotations.

Theorem normalizer_db_sound : forall t v (H_SN : SN t),
    @normalizer t H_SN = v -> normalise t v.
Proof.
    intros t v H_SN H.
Admitted.