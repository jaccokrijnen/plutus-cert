From Autosubst Require Import Autosubst.
From Autosubst Require Export Autosubst.

(** DeBruijn types *)
(** kinds *)
Inductive type : Type :=
  | tp_base : type
  | tp_arrow : type -> type -> type.

(** Types *)
Inductive term :=
  | tmvar (x : var) (* Not nat? *)
  | tmlam (A : type) (s : term) (* In autosubst example: bind term for s?*)
  | tmapp (s t : term).

(** Autosubst *)
(* Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed. *)
(* Instance HSubst_term : HSubst type term. derive. Defined. *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

(* Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed. *)
(* Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed. *)

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.