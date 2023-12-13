Require Import PlutusCert.PlutusIR.
Import PlutusNotations.
Import NamedTerm.

Require Export PlutusCert.PlutusIR.Analysis.BoundVars.

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
  Context {subst_b : string -> Term -> Binding -> Binding}.

  Function subst_bnr' (x : string) (s : Term) (bs : list Binding) : list Binding :=
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
  Function subst_br' (x : string) (s : Term) (bs : list Binding) : list Binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        subst_b x s b :: subst_br' x s bs'
    end.

End SubstBindings.

Function subst (x : string) (s : Term) (t : Term) {struct t} : Term :=
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
  | Constr i ts =>
      Constr i (map (subst x s) ts)
  | Case t ts =>
      Case (subst x s t) (map (subst x s) ts)
  end

with

  (* See note [Assumption of subst_b and subst_br] *)
  subst_b (x : string) (s : Term) (b : Binding) {struct b} : Binding :=
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y T) (subst x s tb)
  | _ => b
  end.

Definition subst_bnr x s bs := (@subst_bnr' subst_b x s bs).
Definition subst_br x s bs := (@subst_br' subst_b x s bs).

Notation "'[' s '/' x ']' t" := (subst x s t) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][b]' b" := (subst_b x s b) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][bnr]' bs" := (@subst_bnr x s bs) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][br]' bs" := (@subst_br  x s bs) (in custom plutus_term at level 20, x constr).


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
  | Constr i ts =>
      Constr i (map (subst x s) ts)
  | Case t ts =>
      Case (subst x s t) (map (subst x s) ts)
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

(** Multi-substitutions of terms *)
Fixpoint msubst (ss : list (string * Term)) (t : Term) : Term :=
  match ss with
  | nil => t
  | (x, s) :: ss' => msubst ss' <{ [s / x] t }>
  end.

Fixpoint msubst_b (ss : list (string * Term)) (b : Binding) : Binding :=
  match ss with
  | nil => b
  | (x, s) :: ss' => msubst_b ss' <{ [s / x][b] b }>
  end.

Fixpoint msubst_bnr (ss : list (string * Term)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (x, s) :: ss' => msubst_bnr ss' <{ [s / x][bnr] bs }>
  end.

Notation "'/[' ss '/]' t" := (msubst ss t) (in custom plutus_term at level 20, ss constr).
Notation "'/[' ss '/][b]' b" := (msubst_b ss b) (in custom plutus_term at level 20, ss constr).
Notation "'/[' ss '/][bnr]' bs" := (msubst_bnr ss bs) (in custom plutus_term at level 20, ss constr).
