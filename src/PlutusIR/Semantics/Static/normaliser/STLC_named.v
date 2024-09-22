
From Equations Require Import Equations.
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Require Import Lia.

Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Ascii.

From PlutusCert Require Import Util.List. (* I don't understand why we need this for ftv defintion*)

(** Types, kinds and substitutions *)
(** kinds *)
Inductive type :=
  | tp_base : type
  | tp_arrow : type -> type -> type.

(** Types *)
Inductive term :=
  | tmvar : string -> term
  | tmlam : string -> type -> term -> term
  | tmapp : term -> term -> term
.

Set Implicit Arguments.

(** Substitutions *)
Function ftv (T : term) : list string :=
    match T with
    | tmvar X =>
        [X]
    | tmlam X K1 T' =>
        remove string_dec X (ftv T')
    | tmapp T1 T2 =>
        ftv T1 ++ ftv T2
    end.

Fixpoint substituteT (X : string) (U T : term) : term :=
  match T with
  | tmvar Y =>
    if X =? Y then U else tmvar Y
  | tmlam Y K1 T' =>
    if X =? Y then tmlam Y K1 T' else tmlam Y K1 (substituteT X U T')
  | tmapp T1 T2 =>
    tmapp (substituteT X U T1) (substituteT X U T2)
  end.

(** * Capture-avoiding substitution of types *)

Definition fresh' (sigma : list (string * term)) (T : term) : string :=
  "a" (* new*)
   ++ (String.concat EmptyString (map fst sigma)) (* keys *)
   ++ (String.concat EmptyString (List.flat_map (compose ftv snd) sigma)) (* values *)
   ++ (String.concat EmptyString (ftv T)). (* term *)

Definition fresh (X : string) (U T : term) : string :=
  "a" ++ X ++ (String.concat EmptyString (ftv U)) ++ (String.concat EmptyString (ftv T)).

Lemma fresh__X : forall X U T,
    X <> fresh X U T.
Proof with eauto.
  intros. intros Hcon.
  induction X; induction (ftv U); induction (ftv T).
  all: simpl in Hcon.
  all: inversion Hcon; subst...
Qed.

Lemma fresh__S : forall X U T,
    ~ In (fresh X U T) (ftv U).
Proof. Abort.

Lemma fresh__T : forall X U T,
    ~ In (fresh X U T) (ftv T).
Proof. Abort.

Definition rename (X Y : string) (T : term) := substituteT X (tmvar Y) T.

Fixpoint size (T : term) : nat :=
  match T with
  | tmvar Y => 1
  | tmlam bX K T0 => 1 + size T0
  | tmapp T1 T2 => 1 + size T1 + size T2
  end.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? s); eauto.
  - destruct (X =? s); simpl; eauto.
Qed.

Equations? substituteTCA (X : string) (U T : term) : term by wf (size T) :=
  substituteTCA X U (tmvar Y) =>
      if X =? Y then U else tmvar Y ;
  substituteTCA X U (tmlam Y K T) =>
      if X =? Y
        then
          tmlam Y K T
        else
          if existsb (String.eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              tmlam Y' K (substituteTCA X U T')
            else
              tmlam Y K (substituteTCA X U T) ;
  substituteTCA X U (tmapp T1 T2) =>
      tmapp (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Defined.