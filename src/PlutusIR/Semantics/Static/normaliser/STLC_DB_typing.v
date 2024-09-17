From PlutusCert Require Import STLC_DB normaliser.Context.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From PlutusCert Require Import STLC_DB.

Global Instance Ids_type : Ids type. unfold Ids. exact (fun s => tp_base). Defined.

Definition ctx := seq type.
Notation "Gamma `_ i" := (normaliser.Context.get Gamma i) (at level 3).

(** Kinding of types *)
Reserved Notation "Δ '|-*db' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_type_db : seq type -> term -> type -> Prop :=
  | K_Var : forall Δ i,
      i < size Δ ->
      Δ |-*db (tmvar i) : (Δ`_i)
  | K_Lam : forall Δ K1 T K2,
      (K1 :: Δ) |-*db T : K2 ->
      Δ |-*db (tmlam K1 T) : (tp_arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-*db T1 : (tp_arrow K1 K2) ->
      Δ |-*db T2 : K1 ->
      Δ |-*db (tmapp T1 T2) : K2
where "Δ '|-*db' T ':' K" := (has_type_db Δ T K).