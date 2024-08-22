(** Strong normalisation proof of non-deterministic STLC with DeBruijn variables *)
From PlutusCert Require Import STLC_DB.
From PlutusCert Require Import STLC_DB_typing.

Require Import Coq.Lists.List.
Import ListNotations.

(** Non-deterministic step relation *)
Inductive step_nd : term -> term -> Prop :=
    | step_beta (A : type) (s t : term) :
        step_nd (tmapp (tmlam A s) t) s.[t/]
    | step_appL s1 s2 t :
        step_nd s1 s2 -> step_nd (tmapp s1 t) (tmapp s2 t)
    | step_appR s t1 t2 :
        step_nd t1 t2 -> step_nd (tmapp s t1) (tmapp s t2)
    | step_abs A s1 s2 :
        step_nd s1 s2 -> step_nd (tmlam A s1) (tmlam A s2).


Inductive SN x : Prop :=
| SNI : (forall y, step_nd x y -> SN y) -> SN x.


Theorem STLC_DB_SN : forall {t T} ,
    [] |-*db t : T -> SN t.
Proof.
Admitted.