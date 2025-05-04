From Coq Require Import Strings.String.
From Coq Require Import Lists.List.

(* Basic types for our language *)
Inductive ty : Type :=
  | Ty_Var : string -> ty
  | Ty_Fun : ty -> ty -> ty.

Inductive kind : Type :=
  | Kind_Base
  | Kind_Arrow : kind -> kind -> kind.

Definition binderTyname := string. (* Just an alias *)

(* Context operations *)
Fixpoint lookup (X : binderTyname) (Δ : list (binderTyname * kind)) : option kind :=
  match Δ with
  | nil => None
  | (Y, K) :: Δ' => if String.eqb X Y then Some K else lookup X Δ'
  end.
(* 1. Keep your existing Prop definition *)
Inductive has_kind_Prop : list (binderTyname * kind) -> ty -> kind -> Prop :=
  | K_Var_Prop : forall Δ X K,
      lookup X Δ = Some K ->
      has_kind_Prop Δ (Ty_Var X) K
  | K_Fun_Prop : forall Δ T1 T2,
      has_kind_Prop Δ T1 Kind_Base ->
      has_kind_Prop Δ T2 Kind_Base ->
      has_kind_Prop Δ (Ty_Fun T1 T2) Kind_Base.

(* 2. Create parallel Set version *)
Inductive has_kind_Set : list (binderTyname * kind) -> ty -> kind -> Set :=
  | K_Var_Set : forall Δ X K,
      lookup X Δ = Some K ->
      has_kind_Set Δ (Ty_Var X) K
  | K_Fun_Set : forall Δ T1 T2,
      has_kind_Set Δ T1 Kind_Base ->
      has_kind_Set Δ T2 Kind_Base ->
      has_kind_Set Δ (Ty_Fun T1 T2) Kind_Base.