Require Import PlutusCert.Language.PlutusIR. 
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** * Capture-avoiding ubstitution of types *)

(** ** Implementation as an inductive datatype *)
Inductive substituteTCA (a : tyname) (U : Ty) : Ty -> Ty -> Prop :=
  | STCA_TyVar1 : 
      substituteTCA a U (Ty_Var a) U
  | STCA_TyVar2 : forall b,
      a <> b ->
      substituteTCA a U (Ty_Var b) (Ty_Var b)
  | STCA_TyFun : forall T1 T1' T2 T2',
      substituteTCA a U T1 T1' ->
      substituteTCA a U T2 T2' ->
      substituteTCA a U (Ty_Fun T1 T2) (Ty_Fun T1' T2')
  | STCA_TyIFix : forall F F' T T',
      substituteTCA a U F F' ->
      substituteTCA a U T T' ->
      substituteTCA a U (Ty_IFix F T) (Ty_IFix F' T')
  | STCA_TyForall1 : forall K T,
      substituteTCA a U (Ty_Forall a K T) (Ty_Forall a K T)
  | STCA_TyForall2 : forall b c K T T',
      a <> b ->
      appears_free_in_Ty b U ->
      ~ appears_free_in_Ty c U ->
      substituteTCA a U (substituteT b (Ty_Var c) T) T' ->
      substituteTCA a U (Ty_Forall b K T) (Ty_Forall c K T')
  | STCA_TyForall3 : forall b K T T',
      a <> b ->
      ~ appears_free_in_Ty b U ->
      substituteTCA a U T T' ->
      substituteTCA a U (Ty_Forall b K T) (Ty_Forall b K T')
  | STCA_TyBuiltin : forall d,
      substituteTCA a U (Ty_Builtin d) (Ty_Builtin d)
  | STCA_TyLam1 : forall K T,
      substituteTCA a U (Ty_Lam a K T) (Ty_Lam a K T)
  | STCA_TyLam2 : forall b c K T T',
      a <> b ->
      appears_free_in_Ty b U ->
      ~ appears_free_in_Ty c U ->
      substituteTCA a U (substituteT b (Ty_Var c) T) T' ->
      substituteTCA a U (Ty_Lam b K T) (Ty_Lam c K T')
  | STCA_TyLam3 : forall b K T T',
      a <> b ->
      ~ appears_free_in_Ty b U ->
      substituteTCA a U T T' ->
      substituteTCA a U (Ty_Lam b K T) (Ty_Lam b K T')
  | STCA_TyApp : forall T1 T1' T2 T2',
      substituteTCA a U T1 T1' ->
      substituteTCA a U T2 T2' ->
      substituteTCA a U (Ty_App T1 T2) (Ty_App T1' T2')
  .

(** * Capture-avoiding multi-substitutions of types *)

Definition env := list (tyname * Ty).

Inductive msubstTCA : env -> Ty -> Ty -> Prop :=
  | msubstTCA_nil : forall T,
      msubstTCA nil T T
  | msubstTCA_cons : forall a U ss T T' T'',
      substituteTCA a U T T' ->
      msubstTCA ss T' T'' ->
      msubstTCA ((a, U) :: ss) T T''.