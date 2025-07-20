From Equations Require Import Equations.

From PlutusCert Require Import PlutusIR Util.

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Local Open Scope list_scope.
Import ListNotations.


(** * Regular substitution of types *)

Fixpoint substituteT (X : string) (U T : ty) : ty :=
  match T with
  | Ty_Var Y =>
    if X =? Y then U else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X U T1) (substituteT X U T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X U F) (substituteT X U T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X U T')
  | Ty_Builtin u =>
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X U T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X U T1) (substituteT X U T2)
  | Ty_SOP Tss =>
    Ty_SOP (map2 (substituteT X U) Tss)
  end.

(** Multi-substitutions of types*)
Fixpoint msubstT (ss : list (string * ty)) (T : ty) : ty :=
  match ss with
  | nil => T
  | (a, T0) :: ss' => msubstT ss' (substituteT a T0 T)
  end.

(** * Capture-avoiding substitution of types *)
Require Import Lia.
Import ListNotations.

From PlutusCert Require Import Analysis.FreeVars.

(* In this file we only talk about type variables in types *)
Definition ftv := Ty.ftv.

Fixpoint tv (t : ty) : list string :=
  match t with
  | Ty_Var x => [x]
  | Ty_Lam x A t => x :: (tv t)
  | Ty_Forall x A t => x :: (tv t)
  | Ty_Fun t1 t2 => tv t1 ++ tv t2
  | Ty_App t1 t2 => tv t1 ++ tv t2
  | Ty_IFix f1 t1 => tv f1 ++ tv t1
  | Ty_Builtin d => []
  | Ty_SOP Tss => 
      flatmap2 tv Tss
  end.

(* Compute (tv (Ty_SOP [[Ty_Var "a"; Ty_Var "b"]; [Ty_Var "c"; Ty_Var "d"]])). *)

Lemma weaken_not_tv_to_not_ftv : forall X T,
  ~ In X (tv T) -> ~ In X (ftv T).
Admitted.


(** Assume that we compute the substitution of U for X in (LamAbs Y K T).
    We reduce the  problem of generating a fresh type variable to generating
    a type variable A such that:

    A <> X /\ ~ In A (ftv U) /\ ~ In A (ftv T)

    We generate a ``fresh'' type variable naively: We concatenate X, all
    free type variables in U and all free type variables in T together.
    By appending an arbitrary letter such as "a" to the result of the previous,
    we get a type variable string which is strictly larger than [X], the
    free type variables in U and the free type variables in T. This means
    that the abovementioned formula holds.

    TODO: The above is only an informal proof, so we should prove freshness
    formally as well.
*)
Definition fresh (X : string) (U T : ty) : string :=
  "a" ++ X ++ (Coq.Strings.String.concat EmptyString (tv U)) ++ (Coq.Strings.String.concat EmptyString (tv T)).

Lemma fresh__X : forall X U T,
    X <> fresh X U T.
Proof with eauto.
  intros. intros Hcon.
  induction X; induction (ftv U); induction (ftv T).
  all: simpl in Hcon.
  all: inversion Hcon; subst...
Qed.

Lemma fresh__S : forall X U T,
    ~ In (fresh X U T) (tv U).
Proof. Admitted.

Lemma fresh__T : forall X U T,
    ~ In (fresh X U T) (tv T).
Proof. Admitted.

Definition rename (X Y : string) (T : ty) := substituteT X (Ty_Var Y) T.

Fixpoint size (T : ty) : nat :=
  match T with
  | Ty_Var Y => 1
  | Ty_Fun T1 T2 => 1 + size T1 + size T2
  | Ty_IFix F T => 1 + size F + size T
  | Ty_Forall bX K T0 => 1 + size T0
  | Ty_Builtin u => 1
  | Ty_Lam bX K T0 => 1 + size T0
  | Ty_App T1 T2 => 1 + size T1 + size T2
  | Ty_SOP Tss => 1 + fold_right2 (fun T acc => size T + acc) 0 Tss
  (* NOTE: Using fold_right: easier to prove with in how it "spits" out a term that is "outside of"  the recursive fold_right*)
  end.

Lemma ty_sop_smaller : forall Tss Ts T,
  In T Ts -> size T < size (Ty_SOP (Ts::Tss)).
Proof.
  intros. simpl. simpl.
  induction Ts.
  - inversion H.
  - destruct H.
    + subst. simpl. lia.
    + simpl. specialize (IHTs H). lia.
Qed.

Lemma ty_sop_le2 : forall Tss T,
  size (Ty_SOP Tss) <= size (Ty_SOP (T::Tss)).
Proof.
  intros. simpl. simpl.
  induction T; simpl; auto.
  lia.
Qed. 

Lemma size_list_smaller : forall (T : ty) (Ts : list ty) (Tss : list (list ty)),
  In T Ts -> In Ts Tss -> size T < size (Ty_SOP Tss).
Proof.
  intros T Ts Tss Hin_Ts Hin_Tss. 
  
  induction Tss.
  - inversion Hin_Tss.
  - destruct Hin_Tss.
    + subst. induction Ts.
      * inversion Hin_Ts.
      * apply ty_sop_smaller. auto.
    +  specialize (IHTss H).
      assert (size (Ty_SOP Tss) <= size (Ty_SOP (a :: Tss))).
      { apply ty_sop_le2. }
      lia.
Qed.

Lemma rename_preserves_size : forall T X Y,
    size T = size (rename X Y T).
Proof.
  intros.
  unfold rename.
  apply PlutusIR.ty__ind with (P := fun T => size T = size (substituteT X (Ty_Var Y) T)); intros; simpl; eauto.
  all: try solve [destruct (X =? X0); simpl; eauto].
  induction H; auto.
  f_equal.
  inversion IHForall.
  induction H; auto.
  inversion IHForall0.
  simpl; auto.
Qed.

(* A version of map that remembers list membership. Necessary in termination argument of substituteTCA*)
Fixpoint map' {A B : Type} (xs : list A) : (forall x : A, In x xs -> B) -> list B :=
  match xs with
  | [] => fun _ => []
  | x :: xs => fun f =>
      f x ((or_introl (eq_refl : x = x)) : In x (x::xs)) :: map' xs (fun (y : A) (Hin : In y xs) => f y (or_intror Hin : In y (x :: xs)))
  end.



(* A version of map2 that remembers list membership. Necessary in termination argument of substituteTCA*)

Equations? substituteTCA (X : string) (U T : ty) : ty by wf (size T) :=
  substituteTCA X U (Ty_Var Y) =>
      if X =? Y then U else Ty_Var Y ;
  substituteTCA X U (Ty_Fun T1 T2) =>
      Ty_Fun (substituteTCA X U T1) (substituteTCA X U T2) ;
  substituteTCA X U (Ty_IFix F T) =>
      Ty_IFix (substituteTCA X U F) (substituteTCA X U T) ;
  substituteTCA X U (Ty_Forall Y K T) =>
      if X =? Y
        then
          Ty_Forall Y K T
        else
          if existsb (eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              Ty_Forall Y' K (substituteTCA X U T')
            else
              Ty_Forall Y K (substituteTCA X U T) ;
  substituteTCA X U (Ty_Builtin u) =>
      Ty_Builtin u ;
  substituteTCA X U (Ty_Lam Y K T) =>
      if X =? Y
        then
          Ty_Lam Y K T
        else
          if existsb (eqb Y) (ftv U)
            then
              let Y' := fresh X U T in
              let T' := rename Y Y' T in
              Ty_Lam Y' K (substituteTCA X U T')
            else
              Ty_Lam Y K (substituteTCA X U T) ;
  substituteTCA X U (Ty_App T1 T2) =>
      Ty_App (substituteTCA X U T1) (substituteTCA X U T2);
  substituteTCA X U (Ty_SOP Tss) => Ty_SOP (map' Tss
         (fun (Ts : list ty) (Hin' : In Ts Tss) => 
            map' Ts
            (fun T Hin => substituteTCA X U T)
          )
         )
  .
Proof.
  all: try solve
    [ lia
    || replace T' with (rename Y Y' T); eauto; rewrite <- rename_preserves_size; eauto
    ].

    eapply size_list_smaller; eauto.
Defined.
