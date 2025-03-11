
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

Inductive term_plut :=
  | plutvar : string -> term_plut
  | plutlam : string -> type -> term_plut -> term_plut
  | plutforall : string -> type -> term_plut -> term_plut
  | plutapp: term_plut -> term_plut -> term_plut
.

(** Substitutions *)
Fixpoint ftv (T : term_plut) : list string :=
    match T with
    | plutvar X =>
        [X]
    | plutlam X K1 T' =>
        remove string_dec X (ftv T')
    | plutforall X K1 T' =>
        remove string_dec X (ftv T')
    | plutapp T1 T2 =>
        ftv T1 ++ ftv T2
    end.


Fixpoint rename (X Y : string) (T : term_plut) :=
  match T with
  | plutvar Z => if X =? Z then plutvar Y else plutvar Z
  | plutlam Z K T0 => if X =? Z then plutlam Z K T0 else plutlam Z K (rename X Y T0)
  | plutforall Z K T0 => if X =? Z then plutforall Z K T0 else plutforall Z K (rename X Y T0)
  | plutapp T1 T2 => plutapp (rename X Y T1) (rename X Y T2)
  end.

(* Size of a term *)

Fixpoint size (T : term_plut) : nat :=
  match T with
  | plutvar Y => 1
  | plutlam bX K T0 => 1 + size T0
  | plutforall bX K T0 => 1 + size T0
  | plutapp T1 T2 => 1 + size T1 + size T2
  end.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  unfold rename.
  induction T; intros; simpl; eauto.
  - destruct (X =? s); eauto.
  - destruct (X =? s); simpl; eauto.
  - destruct (X =? s); simpl; eauto.
Qed.

(* Bound and free type variables *)
Fixpoint tv (s : term_plut) : list string :=
    match s with
    | plutvar x => x::nil
    | plutlam x A s => x :: tv s
    | plutforall x A s => x :: tv s
    | plutapp s t => tv s ++ tv t
    end.

Fixpoint tv_keys_env (sigma : list (string * term_plut)) : list string :=
  match sigma with
  | nil => nil
  | (x, t)::sigma' => x :: (tv t) ++ (tv_keys_env sigma')
  end.

Definition fresh2 (sigma : list (string * term_plut)) (T : term_plut) : string :=
  "a" (* new*)
  ++ String.concat EmptyString (
    tv_keys_env sigma ++ tv T
  ).

Equations? substituteTCA (X : string) (U T : term_plut) : term_plut by wf (size T) :=
  substituteTCA X U (plutvar Y) =>
      if X =? Y then U else plutvar Y ;
  substituteTCA X U (plutlam Y K T) =>
      if X =? Y
        then
          plutlam Y K T
        else
          if existsb (String.eqb Y) (ftv U)
            then
              let Y' := fresh2 ((Y, plutvar Y)::(X, U)::nil) T in
              let T' := rename Y Y' T in
              plutlam Y' K (substituteTCA X U T')
            else
              plutlam Y K (substituteTCA X U T) ;
    substituteTCA X U (plutforall Y K T) =>
        if X =? Y
            then
            plutforall Y K T
            else
            if existsb (String.eqb Y) (ftv U)
                then
                let Y' := fresh2 ((Y, plutvar Y)::(X, U)::nil) T in
                let T' := rename Y Y' T in
                plutforall Y' K (substituteTCA X U T')
                else
                plutforall Y K (substituteTCA X U T) ;
  substituteTCA X U (plutapp T1 T2) =>
      plutapp (substituteTCA X U T1) (substituteTCA X U T2)
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].
Qed.



(* TODO: Removed normal_ty restrictions: we already know they
    are not a problem from our d to nd research*)
Inductive step_plut : term_plut -> term_plut -> Set :=
    | step_plut_beta (X : string) (K : type) (S T : term_plut) :
        step_plut (plutapp (plutlam X K S) T) (substituteTCA X T S) (* conservative substitutions *)
    | step_plut_appL S1 S2 T :
        step_plut S1 S2 -> step_plut (plutapp S1 T) (plutapp S2 T)
    | step_plut_appR S T1 T2 :
        step_plut T1 T2 -> step_plut (plutapp S T1) (plutapp S T2)
    | step_plut_forall bX K S1 S2 :
        step_plut S1 S2 -> step_plut (plutforall bX K S1) (plutforall bX K S2)
    | step_plut_abs bX K T1 T2 :
        step_plut T1 T2 -> step_plut (plutlam bX K T1) (plutlam bX K T2).


(* from annotated stlc to plut*)

Set Implicit Arguments.
