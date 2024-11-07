
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

Definition fresh2 (sigma : list (string * term)) (T : term) : string :=
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

(* TODO: Should we add the assumption that we are always substing in fresh stuff? *)
(* TODO: Fresh with respect to what? *)
Fixpoint mren (rho : list (string * string)) (T : term) : term :=
  match T with
  | tmvar Y => match lookup Y rho with
              | Some Z => tmvar Z
              | None => tmvar Y
              end
  | tmlam Y K1 T_body => let rho' := drop Y rho in (* What if Y in rhs of rho*)
                        tmlam Y K1 (mren rho' T_body)
  | tmapp T1 T2 => tmapp (mren rho T1) (mren rho T2)
end.

Definition rename (X Y : string) (T : term) := mren [(X, Y)] T.

(* Size of a term *)

Fixpoint size (T : term) : nat :=
  match T with
  | tmvar Y => 1
  | tmlam bX K T0 => 1 + size T0
  | tmapp T1 T2 => 1 + size T1 + size T2
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

(** Capture avoiding parallel multi-substitutions *)
    (* We always rename in the lambda, which has two advantages:
      1. We don't have to check if Y a key in sigma, 
      since Y won't exist in T_body after renaming, 
      so the subst will be irrelevant. Hence no "dropping"
      2. We don't have to check if Y in a value of sigma,
         because we will simply always rename.

      We need a new fresh function, since we have multisubstitutions
      fresh' sigma T_body := variable not in
                            - any key of sigma
                            - any value of sigma
                            - T_body
      *)

      (* Idea/problem: Because of the above, identity substitutions refresh variables.
        we could solve this by wrapping this in capms' and removing identity substitutions.

        Not well thought out! TODO
        *)
Equations? capms (sigma : list (string * term)) (T : term) : term by wf (size T) :=
  capms sigma (tmvar Y) := match lookup Y sigma with
                          | Some t => t
                          | None => tmvar Y
                          end;
  capms sigma (tmlam Y K1 T_body) := let Y' := fresh2 ((Y, tmvar Y)::sigma) T_body in (* TODO: should include Y! *)
                                    let T_body' := rename Y Y' T_body in
                                    tmlam Y' K1 (capms sigma T_body');
  capms sigma (tmapp T1 T2) := tmapp (capms sigma T1) (capms sigma T2).
Proof.
  all: try solve
    [ lia
    || replace T_body' with (rename Y Y' T_body); eauto; rewrite <- rename_preserves_size; eauto
    ].
Defined.

Require Import Coq.Program.Equality.

(* Equations? capmsfr_rename X X' T : term by wf (size T) :=
  capmsfr_rename X X' (tmvar Y) := if X =? Y then tmvar X' else tmvar Y;
  capmsfr_rename X X' (tmlam Y K1 T_body) := let Y' := fresh2 [(X, tmvar X')] T_body in
                                        let T_body' := capmsfr_rename Y Y' T_body in
                                        tmlam Y' K1 (capmsfr_rename X X' T_body');
  capmsfr_rename X X' (tmapp T1 T2) := tmapp (capmsfr_rename X X' T1) (capmsfr_rename X X' T2).
Proof.
  all: try solve
    [ lia
    || replace T_body' with (capmsfr_rename Y Y' T_body); eauto; rewrite <- rename_preserves_size; eauto
    ].
    (* still to prove: size T_body' < S (size T_body)
    *) *)

(* 
Lemma capmsfr_rename_preserves_size : forall T X X',
    size T = size (capmsfr_rename X X' T).
Proof.
  intros T X X'.
  induction T; simpl; eauto.
  - destruct (X =? s) eqn:xs; eauto.
    + rewrite capmsfr_rename_equation_1.
      rewrite xs.
      reflexivity.
    + rewrite capmsfr_rename_equation_1.
      rewrite xs.
      reflexivity.
  - rewrite capmsfr_rename_equation_2. simpl.
    rewrite IHT.
    reflexivity.
  - rewrite capmsfr_rename_equation_3. simpl.
    rewrite IHT1, IHT2.
    reflexivity.
Qed. *)

(* 
Since we are working up to alhpa equivalence, why not also freshen the lambda again?

Idea: [x to x'] (\x.\x.x) in the previous definition became
  Y' is fresh.
  T_body' = rename x Y' (\x.x) = \x.x
  ->   \Y'. [x to x'] (\x.x) = \Y'.\Y''.Y''

  but also 

  [x to x'] (\x.\y.y)
  Y' is fresh
  T_body' = rename x Y' (\y.y) = (\y. (rename x Y' y)) = \y. y
  ->    \Y'. [x to x'] (\y. y) = \Y' . \Y''. Y''

  In the new definition:

  [x to x'] (\x.\y.y)
  Y' is fresh
  \Y'. [x to Y', x to x'] (\y.y) = \Y' . \Y''. [y to Y'', x to Y', x to x'] y = \Y'. \Y''. Y''

  

*)
Equations capmsfr (sigma : list (string * term)) (T : term) : term :=
  capmsfr sigma (tmvar Y) := match lookup Y sigma with
                          | Some t => t
                          | None => tmvar Y
                          end;
  capmsfr sigma (tmlam Y K1 T_body) := let Y' := fresh2 sigma T_body in
                                    tmlam Y' K1 (capmsfr ((Y, tmvar Y')::sigma) T_body); 
  capmsfr sigma (tmapp T1 T2) := tmapp (capmsfr sigma T1) (capmsfr sigma T2).


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
Qed.