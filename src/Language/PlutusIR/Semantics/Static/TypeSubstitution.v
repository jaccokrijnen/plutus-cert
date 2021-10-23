Require Import PlutusCert.Language.PlutusIR. 
Import NamedTerm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** * Regular substitution of types *)

Fixpoint substituteT (X : tyname) (S T : Ty) : Ty :=
  match T with
  | Ty_Var Y => 
    if X =? Y then S else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X S T1) (substituteT X S T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X S F) (substituteT X S T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X S T')
  | Ty_Builtin u => 
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X S T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X S T1) (substituteT X S T2)
  end.

(** Multi-substitutions of types*)
Definition envT := list (tyname * Ty).

Fixpoint msubstT (ss : envT) (T : Ty) : Ty :=
  match ss with
  | nil => T
  | (a, T0) :: ss' => msubstT ss' (substituteT a T0 T)
  end.

(** * Capture-avoiding substitution of types *)
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Import Lia.
Import ListNotations.

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

Definition rename (X Y : tyname) (T : Ty) := substituteT X (Ty_Var Y) T.

Fixpoint size (T : Ty) : nat := 
  match T with
  | Ty_Var Y => 1
  | Ty_Fun T1 T2 => 1 + size T1 + size T2
  | Ty_IFix F T => 1 + size F + size T  
  | Ty_Forall bX K T0 => 1 + size T0
  | Ty_Builtin u => 1
  | Ty_Lam bX K T0 => 1 + size T0
  | Ty_App T1 T2 => 1 + size T1 + size T2 
  end.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
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
              let T0' := rename Y Y' T0 in
              Ty_Forall Y' K (substituteTCA X U T0')
            else
              Ty_Forall Y K T0 ;
  substituteTCA X U (Ty_Builtin u) =>
      Ty_Builtin u ;
  substituteTCA X U (Ty_Lam Y K T0) =>
      if X =? Y 
        then 
          Ty_Lam Y K T0 
        else 
          if existsb (eqb Y) (ftv U) 
            then 
              let Y' := fresh U Y in
              let T0' := rename Y Y' T0 in
              Ty_Lam Y' K (substituteTCA X U T0') 
            else
              Ty_Lam Y K (substituteTCA X U T0) ;
  substituteTCA X U (Ty_App T1 T2) => 
      Ty_App (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof. 
  all: try solve 
    [ lia 
    || replace T0' with (rename Y Y' T0); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.