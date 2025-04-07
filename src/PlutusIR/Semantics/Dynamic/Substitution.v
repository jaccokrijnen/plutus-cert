Require Import PlutusCert.PlutusIR.
Import PlutusNotations.

Require Export PlutusCert.PlutusIR.Analysis.BoundVars.
From PlutusCert Require Export Substitution.Class.
From PlutusCert Require Import Util.List.

Import Coq.Lists.List.
Import Coq.Strings.String.

Require Import FunInd.

Local Open Scope string_scope.


(* Note [Assumption of subst_b and subst_br]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   `subst_b x s b` assumes that:
     if b is recursive bindings, x ∉ bvb b
   this is guaranteed by the calling sites in subst and subst_bnr',
   which check for the whole letrec group at once. Therefore the check
   is not repeated here.

   Similarly, `subst_br' x s bs` assumes that
     x ∉ bvbs bs
*)


(** Substitution of terms *)

Section SubstBindings.
  Context {subst_b : string -> term -> binding -> binding}.

  Function subst_bnr' (x : string) (s : term) (bs : list binding) : list binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        if existsb (eqb x) (bvb b)
          then
            subst_b x s b :: bs'
          else
            subst_b x s b :: subst_bnr' x s bs'
    end.

  (* See note [Assumption of subst_b and subst_br] *)
  Function subst_br' (x : string) (s : term) (bs : list binding) : list binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        subst_b x s b :: subst_br' x s bs'
    end.

End SubstBindings.

Function subst (x : string) (s : term) (t : term) {struct t} : term :=
  match t with
  | Let NonRec bs t0 =>
      Let NonRec (@subst_bnr' subst_b x s bs)
        (if existsb (eqb x) (bvbs bs)
          then t0
          else subst x s t0
        )
  | Let Rec bs t0 =>
      if existsb (eqb x) (bvbs bs)
        then
          Let Rec bs t0
        else
          Let Rec (@subst_br' subst_b x s bs) (subst x s t0)
  | Var y =>
      if x =? y
        then s
        else Var y
  | TyAbs bX K t0 =>
      TyAbs bX K (subst x s t0)
  | LamAbs bx T t0 =>
      if x =? bx
        then LamAbs bx T t0
        else LamAbs bx T (subst x s t0)
  | Apply t1 t2 =>
      Apply (subst x s t1) (subst x s t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | TyInst t0 T =>
      TyInst (subst x s t0) T
  | Error T =>
      Error T
  | IWrap F T t0 =>
      IWrap F T (subst x s t0)
  | Unwrap t0 =>
      Unwrap (subst x s t0)
  | Constr T i ts =>
      Constr T i (map (subst x s) ts)
  | Case T t ts =>
      Case T (subst x s t) (map (subst x s) ts)
  end

with

  (* See note [Assumption of subst_b and subst_br] *)
  subst_b (x : string) (s : term) (b : binding) {struct b} : binding :=
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y T) (subst x s tb)
  | _ => b
  end.

Definition subst_bnr x s bs := (@subst_bnr' subst_b x s bs).
Definition subst_br x s bs := (@subst_br' subst_b x s bs).

Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom plutus_term at level 20, x constr).
Notation "'[' x ':=' s ']b' b" := (subst_b x s b) (in custom plutus_term at level 20, x constr).
Notation "'[' x ':=' s ']bnr' bs" := (@subst_bnr x s bs) (in custom plutus_term at level 20, x constr).
Notation "'[' x ':=' s ']br' bs" := (@subst_br  x s bs) (in custom plutus_term at level 20, x constr).


(* Unfolding lemmas *)
(* TODO: do this with equations 1.3 instead. Using "Function" seems to brittle:
  it used to generate subst_equation unfolding lemma, but it changed when I
  added cases for Constr and Case, which use map.
*)

Lemma subst_unfold x s t : subst x s t =
  match t with
  | Let NonRec bs t0 =>
      Let NonRec (@subst_bnr' subst_b x s bs)
        (if existsb (eqb x) (bvbs bs)
          then t0
          else subst x s t0
        )
  | Let Rec bs t0 =>
      if existsb (eqb x) (bvbs bs)
        then
          Let Rec bs t0
        else
          Let Rec (@subst_br' subst_b x s bs) (subst x s t0)
  | Var y =>
      if x =? y
        then s
        else Var y
  | TyAbs bX K t0 =>
      TyAbs bX K (subst x s t0)
  | LamAbs bx T t0 =>
      if x =? bx
        then LamAbs bx T t0
        else LamAbs bx T (subst x s t0)
  | Apply t1 t2 =>
      Apply (subst x s t1) (subst x s t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | TyInst t0 T =>
      TyInst (subst x s t0) T
  | Error T =>
      Error T
  | IWrap F T t0 =>
      IWrap F T (subst x s t0)
  | Unwrap t0 =>
      Unwrap (subst x s t0)
  | Constr T i ts =>
      Constr T i (map (subst x s) ts)
  | Case T t ts =>
      Case T (subst x s t) (map (subst x s) ts)
  end.
Proof.
  destruct t; reflexivity.
Qed.


Lemma subst_b_unfold x s b : subst_b x s b =
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y T) (subst x s tb)
  | _ => b
  end.
Proof.
  destruct b; reflexivity.
Qed.


Instance Subst_subst : Subst (string * term) term := {
  s := fun '(x, t) => subst x t
}.

Instance Subst_subst_b : Subst (string * term) binding := {
  s := fun '(x, t) => subst_b x t
}.

Instance Subst_subst_bs : Subst (string * term) (list binding) := {
  s := fun '(x, t) => subst_bnr x t
}.


(** Multi-substitutions of terms *)
Fixpoint msubst (ss : list (string * term)) (t : term) : term :=
  match ss with
  | nil => t
  | (x, s) :: ss' => msubst ss' ((x, s) ⊙ t)
  end.

Fixpoint msubst_b (ss : list (string * term)) (b : binding) : binding :=
  match ss with
  | nil => b
  | (x, s) :: ss' => msubst_b ss' <{ [x := s]b b }>
  end.

Fixpoint msubst_bnr (ss : list (string * term)) (bs : list binding) : list binding :=
  match ss with
  | nil => bs
  | (x, s) :: ss' => msubst_bnr ss' <{ [x := s]bnr bs }>
  end.

Notation "'[' ss ']*' t" := (msubst ss t) (in custom plutus_term at level 20, ss constr).
Notation "'[' ss ']*b' b" := (msubst_b ss b) (in custom plutus_term at level 20, ss constr).
Notation "'[' ss ']*bnr' bs" := (msubst_bnr ss bs) (in custom plutus_term at level 20, ss constr).



Instance Subst_msubst : Subst (list (string * term)) term := {
  s := msubst
}.

Instance Subst_msubst_b : Subst (list (string * term)) binding := {
  s := msubst_b
}.

Instance Subst_msubst_bnr : Subst (list (string * term)) (list binding) := {
  s := msubst_bnr
}.


Instance Drop_string : Drop string term := {
  d := drop
}.

Instance Drop_strings : Drop (list string) term := {
  d := mdrop
}.

Instance Drop_bvbs : Drop (list binding) term := {
  d := fun bs => mdrop (bvbs bs)
}.

Instance Drop_b : Drop binding term := {
  d := fun b => mdrop (bvb b)
}.

Instance Drop_bvbs_ty : Drop (list binding) ty := {
  d := fun bs => mdrop (bvbs bs)
}.

Instance Drop_b_ty : Drop binding ty := {
  d := fun b => mdrop (bvb b)
}.


Create HintDb subst.
Hint Rewrite subst_unfold : subst.

Create HintDb subst_b.
Hint Rewrite subst_b_unfold : subst.
