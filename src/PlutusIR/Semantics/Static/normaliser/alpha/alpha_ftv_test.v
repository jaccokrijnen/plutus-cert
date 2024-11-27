
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

From PlutusCert Require Import Util.List freshness. (* I don't understand why we need this for ftv defintion*)

Inductive term :=
  | tmvar : string -> term
  | tmlam : string -> term -> term.

Function ftv (T : term) : list string :=
    match T with
    | tmvar X =>
        [X]
    | tmlam X T' =>
        remove string_dec X (ftv T')
    end.

(* No alpha var refl, so we no longer have AlphaVar [] x x for any x
    In other words: free variables are always in the list. *)
Inductive AlphaVar : list (string * string) -> string -> string -> Set :=
| alpha_var_cons z w sigma :
    (* x = z ->
    y = w -> *)
    AlphaVar ((z, w) :: sigma) z w
| alpha_var_diff x y z w sigma :
    x <> z -> 
    y <> w -> 
    AlphaVar sigma z w -> 
    AlphaVar ((x, y) :: sigma) z w.

Inductive Alpha : list (string * string) -> term -> term -> Set :=
| alpha_var x y sigma : 
    AlphaVar sigma x y -> 
    Alpha sigma (tmvar x) (tmvar y)
| alpha_lam x y s1 s2 sigma :
    Alpha ((x, y) :: sigma) s1 s2 -> 
    Alpha sigma (tmlam x s1) (tmlam y s2).

Lemma uhm (x x0 z y : string) :
 x0 <> x -> y <> x -> AlphaVar ((x0, y)::(x, y)::nil) x z -> False.
Proof.
 intros.
 inversion H1; subst.
 - contradiction H. reflexivity.
 - inversion H9. subst. contradiction. subst. contradiction.
Qed.

Require Import Coq.Program.Equality.

Lemma alpha_preserves_ftv'' {x x' s s' ren } :
  In x (ftv s) ->
  Alpha ren s s' ->
  AlphaVar ren x x' ->
  In x' (ftv s').
Proof.
    intros.
    induction H0; subst.
    - admit.
    - 
    (* We know (x, x') in sigma by no alpha_refl
    
    So we know (x, x') in (x0, y)::sigma.

    Suppose x' = y.

    Then we know

    (x,y) in (x0,y)::sigma.

    For simplicity, let sigma=(x,y)

    Then Alpha ((x0, y) :: sigma) s1 s2 will at some point encounter (tmvar x).

    But there is no rule then to map it to something in s2. If in s2 we then have (tmvar y), we cannot
    use alpha_var_diff since we do not y = y.
    also not alpha_var cons since not (x0 = x).


    If x in s1 and Alpha ((x0, y):: sigma) s1 s2,

    Then there exists sigma',z s.t. AlphaVar (sigma'::(x0,y)::sigma) x z
    where x notin keys sigma'.


    *)