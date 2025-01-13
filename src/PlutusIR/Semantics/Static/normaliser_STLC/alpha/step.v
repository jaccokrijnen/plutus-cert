From PlutusCert Require Import STLC_named ARS.
From Coq Require Import Strings.String.
Local Open Scope string_scope.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.

(* TODO: Used to be Prop. Ask Jacco*)
Inductive step : term -> term -> Set :=
| step_beta (x : string) (A : type) (s t : term) :
    step (tmapp (tmlam x A s) t) ( [x := t] s)
| step_appL s1 s2 t :
    step s1 s2 -> step (tmapp s1 t) (tmapp s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (tmapp s t1) (tmapp s t2)
| step_abs x A s1 s2 :
    step s1 s2 -> step (tmlam x A s1) (tmlam x A s2).

Lemma step_ebeta x A s t u : 
  u = ([x := t] s) -> step (tmapp (tmlam x A s) t) u.
Proof. move->. exact: step_beta. Qed.


Inductive star {e : term -> term -> Set } (x : term) : term -> Set :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.


(** **** Many-Step Reduction 
TODO: See if we can use the star from autosubst ARS again. (uses Prop instead of Set)
*)
Definition red := @star step.

Lemma star_trans y x z : red x y -> red y z -> red x z.
Proof. move=> A. elim=> //={z} y' z _. exact: starSE. Qed.



(* Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x). *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (tmapp s1 t1) (tmapp s2 t2).
Proof.
  
  move=> A B. apply: (star_trans (tmapp s2 t1)).
  - induction A.
    + exact: starR.
    + eapply starSE.
      * exact IHA.
      * now apply step_appL.
  - induction B.
    + exact: starR.
    + eapply starSE.
      * exact IHB.
      * now apply step_appR.
Qed.

Lemma red_abs x A s1 s2 : 
  red s1 s2 -> red (tmlam x A s1) (tmlam x A s2).
(* Proof. apply: star_hom => x' y'. exact: step_abs. Qed. *)
Proof. 
  move=> B.
  induction B.
  + apply starR.
  + eapply starSE.
    * exact IHB.
    * now apply step_abs.
Qed.