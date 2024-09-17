(* Normalizer for the named simply typed lambda calculus*)
From PlutusCert Require Import STLC_named.
From PlutusCert Require Import STLC_named_typing.
From PlutusCert Require Import Normalizer_STLC_DB.
From PlutusCert Require Import named_DB_iso.
From PlutusCert Require Import SN_F.

Require Import Coq.Lists.List.
Import ListNotations.

(* Does this mean that we only allow empty list well_typedness? *)
Definition normalizer (T : type) (t : term) (H_wt : has_type [] t T) : term :=
  let t_db := toDB t in
  let H_wt_db := toDB_has_type (H_wt) in (* toDB iso preserves well-typedness*)
  let H_SN := strong_normalization (H_wt_db)  in (* Well typed means strongly normalizing *)
  let v_db := Normalizer_STLC_DB.normalizer (toDB t) H_SN in
  fromDB v_db.