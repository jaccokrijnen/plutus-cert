From Autosubst Require Import Autosubst.
From Autosubst Require Export Autosubst.

From Coq Require Import List.
Import ListNotations.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetFacts.

Module NatSet := FSetAVL.Make(Nat_as_OT).
Module NatSetFacts := FSetFacts.Facts(NatSet).


(** DeBruijn types *)
(** kinds *)
Inductive type : Type :=
  | tp_base : type
  | tp_arrow : type -> type -> type.

Global Instance Ids_type : Ids type. unfold Ids. exact (fun s => tp_base). Defined.

(** Types *)
Inductive term :=
  | tmvar (x : var) (* Not nat? *)
  | tmlam (A : type) (s : {bind term}) (* In autosubst example: bind term for s?*)
  | tmapp (s t : term).

Fixpoint fv (t : term) : NatSet.t :=
  match t with
  | tmvar x => NatSet.singleton x
  | tmlam A s => NatSet.fold (fun x acc => if Nat.eqb x 0 then acc else NatSet.add (x - 1) acc) (fv s) NatSet.empty
  | tmapp s t => NatSet.union (fv s) (fv t)
  end.


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