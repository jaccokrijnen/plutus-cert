From PlutusCert Require Import Normalisation_STLC_named.
From PlutusCert Require Import Normalizer_STLC_named.
From PlutusCert Require Import Normalisation_STLC_DB.
From PlutusCert Require Import Normalisation_STLC_DB_sound.
From PlutusCert Require Import named_DB_iso.
From PlutusCert Require Import STLC_DB_typing.
From PlutusCert Require Import STLC_named_typing.

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

Module N := STLC_named.
Module D := STLC_DB.


(* Uhm, not so easy.
    For closed terms it should be rather straightforward? 
    Then you have fromDB (\. t) = \. (fromDB t)?
    But then how do you prove it by induction?
    Probably as difficult as SN? *)

(* Other approach? Work through steps? No, for that we need completeness (of DB, so maybe it is possible)*)
Lemma normaliseDB_then_normalise : forall t_db v_db K,
    [] |-*db t_db : K -> (* do we need this, and do we need an open environment? *)
    Normalisation_STLC_DB.normalise t_db v_db -> 
    Normalisation_STLC_named.normalise (fromDB t_db) (fromDB v_db).
Proof.

Admitted.

Lemma test : forall t_db v_db,
    Normalisation_STLC_DB.normalise (toDB t_db) (toDB v_db) ->
    Normalisation_STLC_named.normalise t_db v_db.
Proof.

Admitted.

(* Running normalizer on named STLC results in a value that
    satisfies the normalise relation *)
Theorem normalizer_named_sound : forall t T v H_wt,
    Normalizer_STLC_named.normalizer T t H_wt = v -> Normalisation_STLC_named.normalise t v.
Proof.
    intros t T v H_wt H.
    assert (toDB (normalizer T t H_wt) = toDB v).
    {
        rewrite H. reflexivity.
    }
    unfold normalizer in H0.
    rewrite named_DB_iso_right in H0.
    apply normalizer_db_sound in H0.
    apply test in H0.
    assumption.
Qed.