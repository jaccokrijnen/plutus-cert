
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
From PlutusCert Require PlutusIRSOP.

Inductive USort := Lam | ForAll.
Inductive BSort := App | IFix | Fun.

(** Types, maybe rename app and lam, since they are now generic *)
Inductive term :=
  | tmvar : string -> term
  | tmlam {USort : USort} : string -> PlutusIRSOP.kind -> term -> term
  | tmapp {BSort : BSort} : term -> term -> term
  | tmbuiltin : PlutusIRSOP.DefaultUni -> term
.


Set Implicit Arguments.

(* Set Implicit Arguments. *)

(** Substitutions *)
Function ftv (T : term) : list string :=
    match T with
    | tmvar X =>
        [X]
    | tmlam X K1 T' =>
        remove string_dec X (ftv T')
    | tmapp T1 T2 =>
        ftv T1 ++ ftv T2
    | tmbuiltin _ => []
    end.

Fixpoint btv (T : term) : list string :=
    match T with
    | tmvar X =>
        []
    | tmlam X K1 T' =>
      X :: btv T'
    | tmapp T1 T2 =>
        btv T1 ++ btv T2
    | tmbuiltin _ => []
    end.

(* Bound and free type variables *)
Fixpoint tv (s : term) : list string :=
  match s with
  | tmvar x => x::nil
  | tmlam x A s => x :: tv s
  | tmapp s t => tv s ++ tv t
  | tmbuiltin _ => nil
  end.

(** * Capture-avoiding substitution of types *)

Fixpoint tv_keys_env (sigma : list (string * term)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (tv t) ++ (tv_keys_env sigma')
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

(* TODO: REMOVE MREN, WE NEVER HAVE MULTIPLE RENAMINGS*)
Fixpoint mren (rho : list (string * string)) (T : term) : term :=
  match T with
  | tmvar Y => match lookup Y rho with
              | Some Z => tmvar Z
              | None => tmvar Y
              end
  | @tmlam B Y K1 T_body => let rho' := drop Y rho in (* What if Y in rhs of rho*)
                        @tmlam B Y K1 (mren rho' T_body)
  | @tmapp B T1 T2 => @tmapp B (mren rho T1) (mren rho T2)
  | tmbuiltin d => tmbuiltin d
end.

Definition rename (X Y : string) (T : term) := mren [(X, Y)] T.

(* Size of a term *)

Fixpoint size (T : term) : nat :=
  match T with
  | tmvar Y => 1
  | tmlam bX K T0 => 1 + size T0
  | tmapp T1 T2 => 1 + size T1 + size T2
  | tmbuiltin _ => 1
  end.

Lemma mren_id s : mren nil s = s.
Proof. 
  induction s; simpl; eauto.
  - rewrite IHs.
    reflexivity.
  - rewrite IHs1, IHs2.
    reflexivity.
Qed.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? s); eauto.
  - destruct (X =? s); simpl; eauto.
    rewrite mren_id.
    reflexivity.
Qed.

Equations? substituteTCA (X : string) (U T : term) : term by wf (size T) :=
  substituteTCA X U (tmvar Y) =>
      if X =? Y then U else tmvar Y ;
  substituteTCA X U (@tmlam B Y K T) =>
      if X =? Y
        then
          @tmlam B Y K T
        else
          if existsb (String.eqb Y) (ftv U)
            then
              let Y' := fresh2 ((X, U)::nil) T in
              let T' := rename Y Y' T in
              @tmlam B Y' K (substituteTCA X U T')
            else
              @tmlam B Y K (substituteTCA X U T) ;
  substituteTCA X U (@tmapp B T1 T2) =>
      @tmapp B (substituteTCA X U T1) (substituteTCA X U T2) ;
  substituteTCA X U (tmbuiltin d) => tmbuiltin d
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.

