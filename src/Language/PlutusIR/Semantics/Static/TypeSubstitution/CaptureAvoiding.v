Require Import PlutusCert.Language.PlutusIR. 
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.

From Coq Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** * Capture-avoiding substitution of types *)
Fixpoint ftv (T : Ty) : list tyname :=
  match T with
  | Ty_Var X => 
      [X]
  | Ty_Fun T1 T2 =>
      ftv T1 ++ ftv T2
  | Ty_IFix F T =>
      ftv F ++ ftv T
  | Ty_Forall X K T' =>
      remove string_dec X (ftv T')
  | Ty_Builtin u => 
      []
  | Ty_Lam X K1 T' =>
      remove string_dec X (ftv T')
  | Ty_App T1 T2 =>
      ftv T1 ++ ftv T2
  end.

(* TODO: Actually generate a fresh type variable *)
Definition fresh (T : Ty) (X : tyname) : tyname := "a".

Fixpoint size (T : Ty) := 
  match T with
  | Ty_Var Y => 1
  | Ty_Fun T1 T2 => 1 + size T1 + size T2
  | Ty_IFix F T => 1 + size F + size T  
  | Ty_Forall bX K T0 => 1 + size T0
  | Ty_Builtin u => 1
  | Ty_Lam bX K T0 => 1 + size T0
  | Ty_App T1 T2 => 1 + size T1 + size T2 
  end.

Lemma rename_preserves_size : forall T X U,
    size U = 1 ->
    size T = size (substituteT X U T).
Proof.
  induction T; intros; simpl; eauto.
  - destruct (X =? t); eauto.
  - destruct (X =? b); simpl; eauto.
  - destruct (X =? b); simpl; eauto.
Qed.

Equations? substituteTCA (X : tyname) (U T : Ty) : Ty by wf (size T) :=
  substituteTCA X U (Ty_Var Y) => 
      if X =? Y then U else Ty_Var Y ;
  substituteTCA X U (Ty_Fun T1 T2) =>
      Ty_Fun (substituteTCA X U T1) (substituteTCA X U T2) ;
  substituteTCA X U (Ty_IFix F T) =>
      Ty_IFix (substituteTCA X U F) (substituteTCA X U T) ;
  substituteTCA X U (Ty_Forall Y K T0) =>
      if X =? Y 
        then 
          Ty_Forall Y K T0
        else 
          if existsb (eqb Y) (ftv U) 
            then 
              let Y' := fresh U Y in
              let T0' := substituteT Y (Ty_Var Y') T0 in
              Ty_Forall Y K (substituteTCA X U T0')
            else
              Ty_Forall Y K T0 ;
  substituteTCA X U (Ty_Builtin u) =>
      Ty_Builtin u ;
  substituteTCA X U (Ty_Lam Y K1 T0) =>
      if X =? Y 
        then 
          Ty_Lam Y K1 T0 
        else 
          if existsb (eqb Y) (ftv U) 
            then 
              let Y' := fresh U Y in
              let T0' := substituteT Y (Ty_Var Y') T0 in
              Ty_Lam Y K1 (substituteTCA X U T0') 
            else
              Ty_Lam Y K1 (substituteTCA X U T0) ;
  substituteTCA X U (Ty_App T1 T2) => 
      Ty_App (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof. 
  all: try solve 
    [ lia 
    || replace T0' with (substituteT Y (Ty_Var Y') T0); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.

(** ** Implementation as an inductive datatype *)
Inductive substituteTCA' (a : tyname) (U : Ty) : Ty -> Ty -> Prop :=
  | STCA_TyVar1 : 
      substituteTCA' a U (Ty_Var a) U
  | STCA_TyVar2 : forall b,
      a <> b ->
      substituteTCA' a U (Ty_Var b) (Ty_Var b)
  | STCA_TyFun : forall T1 T1' T2 T2',
      substituteTCA' a U T1 T1' ->
      substituteTCA' a U T2 T2' ->
      substituteTCA' a U (Ty_Fun T1 T2) (Ty_Fun T1' T2')
  | STCA_TyIFix : forall F F' T T',
      substituteTCA' a U F F' ->
      substituteTCA' a U T T' ->
      substituteTCA' a U (Ty_IFix F T) (Ty_IFix F' T')
  | STCA_TyForall1 : forall K T,
      substituteTCA' a U (Ty_Forall a K T) (Ty_Forall a K T)
  | STCA_TyForall2 : forall b c K T T',
      a <> b ->
      appears_free_in_Ty b U ->
      ~ appears_free_in_Ty c U ->
      substituteTCA' a U (substituteT b (Ty_Var c) T) T' ->
      substituteTCA' a U (Ty_Forall b K T) (Ty_Forall c K T')
  | STCA_TyForall3 : forall b K T T',
      a <> b ->
      ~ appears_free_in_Ty b U ->
      substituteTCA' a U T T' ->
      substituteTCA' a U (Ty_Forall b K T) (Ty_Forall b K T')
  | STCA_TyBuiltin : forall d,
      substituteTCA' a U (Ty_Builtin d) (Ty_Builtin d)
  | STCA_TyLam1 : forall K T,
      substituteTCA' a U (Ty_Lam a K T) (Ty_Lam a K T)
  | STCA_TyLam2 : forall b c K T T',
      a <> b ->
      appears_free_in_Ty b U ->
      ~ appears_free_in_Ty c U ->
      substituteTCA' a U (substituteT b (Ty_Var c) T) T' ->
      substituteTCA' a U (Ty_Lam b K T) (Ty_Lam c K T')
  | STCA_TyLam3 : forall b K T T',
      a <> b ->
      ~ appears_free_in_Ty b U ->
      substituteTCA' a U T T' ->
      substituteTCA' a U (Ty_Lam b K T) (Ty_Lam b K T')
  | STCA_TyApp : forall T1 T1' T2 T2',
      substituteTCA' a U T1 T1' ->
      substituteTCA' a U T2 T2' ->
      substituteTCA' a U (Ty_App T1 T2) (Ty_App T1' T2')
  .

(** * Capture-avoiding multi-substitutions of types *)

Definition env := list (tyname * Ty).

Inductive msubstTCA : env -> Ty -> Ty -> Prop :=
  | msubstTCA_nil : forall T,
      msubstTCA nil T T
  | msubstTCA_cons : forall a U ss T T' T'',
      substituteTCA' a U T T' ->
      msubstTCA ss T' T'' ->
      msubstTCA ((a, U) :: ss) T T''.