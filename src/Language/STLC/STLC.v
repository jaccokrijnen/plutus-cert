
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

From PlutusCert Require Import Util.List Kinding.Kinding. (* I don't understand why we need this for ftv defintion*)

Inductive USort := Lam | ForAll.
Inductive BSort := App | IFix | Fun.

(** Types, maybe rename app and lam, since they are now generic *)
Inductive term :=
  | tmvar : string -> term
  | tmabs {USort : USort} : string -> PlutusIR.kind -> term -> term
  | tmbin {BSort : BSort} : term -> term -> term
  | tmbuiltin : PlutusIR.DefaultUni -> term
.


Set Implicit Arguments.

(* Set Implicit Arguments. *)

(** Substitutions *)
Function ftv (T : term) : list string :=
    match T with
    | tmvar X =>
        [X]
    | tmabs X K1 T' =>
        remove string_dec X (ftv T')
    | tmbin T1 T2 =>
        ftv T1 ++ ftv T2
    | tmbuiltin _ => []
    end.

Fixpoint btv (T : term) : list string :=
    match T with
    | tmvar X =>
        []
    | tmabs X K1 T' =>
      X :: btv T'
    | tmbin T1 T2 =>
        btv T1 ++ btv T2
    | tmbuiltin _ => []
    end.

(* Bound and free type variables *)
Fixpoint tv (s : term) : list string :=
  match s with
  | tmvar x => x::nil
  | tmabs x A s => x :: tv s
  | tmbin s t => tv s ++ tv t
  | tmbuiltin _ => nil
  end.

(** * Capture-avoiding substitution of types *)

Fixpoint tv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (tv t) ++ (tv_keys_env sigma')
  end.

Fixpoint ftv_keys_env (sigma : list (string * term)) : list string :=
match sigma with
| nil => nil
| (x, t)::sigma' => x :: (ftv t) ++ (ftv_keys_env sigma')
end.

Definition fresh2 (sigma : list (string * term)) (T : term) : string :=
  "a" (* new*)
  ++ String.concat EmptyString (
    tv_keys_env sigma ++ tv T
  ).

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

Fixpoint rename (X X' : string) (T : term) := 
  match T with
  | tmvar Y => if X =? Y then tmvar X' else tmvar Y
  | @tmabs B Y K1 T_body => if X =? Y then
                              @tmabs B Y K1 T_body
                            else 
                              @tmabs B Y K1 (rename X X' T_body)
  | @tmbin B T1 T2 => @tmbin B (rename X X' T1) (rename X X' T2)
  | tmbuiltin d => tmbuiltin d
end.

(* Size of a term *)

Fixpoint size (T : term) : nat :=
  match T with
  | tmvar Y => 1
  | tmabs bX K T0 => 1 + size T0
  | tmbin T1 T2 => 1 + size T1 + size T2
  | tmbuiltin _ => 1
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
  substituteTCA X U (@tmabs B Y K T) =>
      if X =? Y
        then
          @tmabs B Y K T
        else
          if existsb (String.eqb Y) (ftv U)
            then
              let Y' := fresh2 ((X, U)::nil) T in
              let T' := rename Y Y' T in
              @tmabs B Y' K (substituteTCA X U T')
            else
              @tmabs B Y K (substituteTCA X U T) ;
  substituteTCA X U (@tmbin B T1 T2) =>
      @tmbin B (substituteTCA X U T1) (substituteTCA X U T2) ;
  substituteTCA X U (tmbuiltin d) => tmbuiltin d
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.

