(* Isomorphism between named STLC and DeBruijn STLC *)
From PlutusCert Require Import STLC_named.
From PlutusCert Require Import STLC_DB.
From PlutusCert Require Import STLC_named_typing.
From PlutusCert Require Import STLC_DB_typing.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Definition fromDB (t_db : STLC_DB.term) : (STLC_named.term) :=
    match t_db with
    | _ => STLC_named.tmvar "hoi" (* mock *)
    end
.

Definition toDB (t_named : STLC_named.term) : (STLC_DB.term) :=
    match t_named with
    | _ => STLC_DB.tmvar 0 (* mock *)
    end
.

Definition toDB_type (T_named : STLC_named.type) : (STLC_DB.type) :=
    match T_named with
    | _ => tp_base (* mock *)
    end.

Theorem toDB_has_type : forall {t T} ,
    has_type [] t T -> has_type_db [] (toDB t) (toDB_type T).
Proof.
Admitted.

Theorem named_DB_iso_left : forall t_named,
    fromDB (toDB t_named) = t_named.
Proof.
Admitted.

Theorem named_DB_iso_right : forall t_db,
    toDB (fromDB t_db) = t_db.
Proof.
Admitted.
