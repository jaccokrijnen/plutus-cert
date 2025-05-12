Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

From PlutusCert Require Import Util.

Definition map2 {A B : Type} (f : A -> B) (ll : list (list A)) : list (list B) :=
  List.map (List.map f) ll.

Inductive NoneSetPair {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
  | NoneSP_nil : NoneSetPair P nil nil
  | NoneSP_cons : forall x y xs ys, ~ (P x y) -> NoneSetPair P xs ys -> NoneSetPair P (x :: xs) (y :: ys).

Inductive ForallSet {A : Type} (P : A -> Type) : list A -> Type :=
| ForallS_nil : ForallSet P nil
| ForallS_cons : forall x xs, P x -> ForallSet P xs -> ForallSet P (x :: xs).


(* ForallT for Props *)
Inductive ForallP22 {A : Type} (P : A -> Prop) : list (list A) -> Prop :=
  | ForallP2_nil : ForallP22 P (nil : list (list A))
  | ForallP2_cons : forall {x : list A} {l : list (list A)},
                  ForallP P x -> ForallP22 P l -> ForallP22 P (x :: l).

Inductive ForallSet2 {A : Type} (P : A -> Set) : list (list A) -> Type :=
| ForallS2_nil : ForallSet2 P nil
| ForallS2_cons : forall x xs, ForallSet P x -> ForallSet2 P xs -> ForallSet2 P (x :: xs).

Inductive ForallSetPair {A B : Type} (P : A -> B -> Type) : list A -> list B -> Type :=
| ForallSP_nil : ForallSetPair P nil nil
| ForallSP_cons : forall x y xs ys, P x y -> ForallSetPair P xs ys -> ForallSetPair P (x :: xs) (y :: ys).

Inductive ForallSetPair2 {A B : Type} (P : A -> B -> Type) : list (list A) -> list (list B) -> Type :=
| ForallSP2_nil : ForallSetPair2 P nil nil
| ForallSP2_cons : forall x y xs ys, ForallSetPair P x y -> ForallSetPair2 P xs ys -> ForallSetPair2 P (x :: xs) (y :: ys).

Definition concat2 {A : Type} (l : list (list (list A))) : list A :=
  List.flat_map (@List.concat A) l.

(* Using convoluted fold_left version so that termination checker has a good time*)
Definition flatmap2 {A B : Type} (f : A -> list B) (l : list (list A)) : list B :=
  fold_right (fun (Ts : (list (A))) (acc : list (B)) => List.app

                    ((fold_right (fun (T : A) (acc2 : list (B))  => List.app (f T) acc2) (nil : list (B) )) Ts) acc
                ) (nil : list (B)) l.

Definition fold_right2 {A B : Type} (f : A -> B -> B) (acc : B) (l : list (list A)) : B :=
  fold_right (fun (Ts : list A) (acc2 : B) => fold_right f acc2 Ts) acc l.