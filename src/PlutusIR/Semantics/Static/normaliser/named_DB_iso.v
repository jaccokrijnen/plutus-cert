(* Isomorphism between named STLC and DeBruijn STLC *)
From PlutusCert Require Import STLC_named.
From PlutusCert Require Import STLC_DB.
From PlutusCert Require Import STLC_named_typing.
From PlutusCert Require Import STLC_DB_typing.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetFacts.

Module N := STLC_named.
Module D := STLC_DB.

Fixpoint my_fresh (fv : list string) : string :=
    match fv with
    | [] => "a"
    | x :: xs => "a" ++ my_fresh xs
    end.

(** We should let them use the same type or coerce them?*)
Fixpoint fromDB_type (T_db : D.type) : (N.type) :=
    match T_db with
    | tp_base => N.tp_base (* mock *)
    | tp_arrow T1 T2 => N.tp_arrow (fromDB_type T1) (fromDB_type T2)
    end.

(** We should let them use the same type or coerce them?*)
Fixpoint toDB_type (T_named : N.type) : (D.type) :=
    match T_named with
    | N.tp_base => tp_base (* mock *)
    | N.tp_arrow T1 T2 => tp_arrow (toDB_type T1) (toDB_type T2)
    end.

Fixpoint create_free_vars (n : nat) : list string :=
    match n with
    | 0 => []
    | S n' => "a" :: (map (fun x => String.append "a" x) (create_free_vars n'))
    end.

(* Assumes that if there are n free vars in STLC_DB term, then they are numberd 0 to n - 1*)
Fixpoint fromDB' (t_db : D.term) (fv : list string) : (N.term) :=
    match t_db with
    | D.tmvar i => N.tmvar (nth i fv "cant happen")
    | D.tmapp t1 t2 => N.tmapp (fromDB' t1 fv) (fromDB' t2 fv)
    | D.tmlam T t => N.tmlam (my_fresh fv) (fromDB_type T) (fromDB' t (my_fresh fv :: fv))
    end.

Definition fromDB (t_db : D.term) : (N.term) :=
(* We cannot create fresh vars for the free vars in t_db on the fly.
        Take e.g. app (app 0 1) (app 1 0)
        Could we do this if we first do app 0 1, which creates new free vars, and pass those along?
        Sounds monadic*)
    let fv_db := D.fv t_db in
    let fv_named := create_free_vars (D.NatSet.cardinal fv_db) in
    fromDB' t_db fv_named.

(* Should be (\ "aa". "a") "a"*)
Eval compute in (fromDB (tmapp (tmlam tp_base (tmvar 1)) (tmvar 0))).
(* Should be (\ "aaa". "aa") "a"*)
Eval compute in (fromDB (tmapp (tmlam tp_base (tmvar 2)) (tmvar 0))). 

(* Should be ("a" "aa") ("aa" "a")*)
Eval compute in (fromDB (tmapp (tmapp (tmvar 0) (tmvar 1)) (tmapp (tmvar 1) (tmvar 0)))).


Fixpoint nth_index_or_0 (l : list string) (n : string) : nat :=
  match l with
  | [] => 0 (* cant happen: 
  Multiple options to fix this:
  - Predicaat: closed: Named -> Type, checks if a named term contains a free variable that is not in the term.
  
  *)
  | x :: xs => if x =? n then 0 else S (nth_index_or_0 xs n)
  end.

Fixpoint toDB' (t_named : N.term) (fv : list string) : (D.term) :=
    match t_named with
    | N.tmvar x => D.tmvar (nth_index_or_0 fv x)
    | N.tmapp t1 t2 => D.tmapp (toDB' t1 fv) (toDB' t2 fv)
    | N.tmlam x T t => D.tmlam (toDB_type T) (toDB' t (x :: (remove string_dec x fv)))
    end.

Definition toDB (t_named : N.term) : (D.term) :=
    toDB' t_named [].

(* Should be (\ "aa". "a") "a"*)

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
