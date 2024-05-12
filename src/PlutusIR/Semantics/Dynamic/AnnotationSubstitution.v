Require Import PlutusCert.PlutusIR.
Import PlutusNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** Substitution of types in type annotations *)

Section SubstABindings.
  Context {substAb : string -> Ty -> Binding -> Binding}.

  Fixpoint substA_bnr' (X : string) (U : Ty) (bs : list Binding) : list Binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        if existsb (eqb X) (btvb b)
          then
            substAb X U b :: bs'
          else
            substAb X U b :: substA_bnr' X U bs'
    end.

  Fixpoint substA_br' (X : string) (U : Ty) (bs : list Binding) : list Binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        substAb X U b :: substA_br' X U bs'
    end.

End SubstABindings.

Section SubstAConstructors.

  Definition substA_c (X : string) (U : Ty) (c : VDecl) : VDecl :=
    match c with
    | VarDecl bx T =>
        VarDecl bx (substituteT X U T)
    end.

  Definition substA_cs (X : string) (U : Ty) (cs : list VDecl) : list VDecl :=
    map (substA_c X U) cs.

End SubstAConstructors.


Fixpoint substA (X : string) (U : Ty) (t : Term) {struct t} : Term :=
  match t with
  | Let NonRec bs t0 =>
      Let NonRec (@substA_bnr' substA_b X U bs)
        (if existsb (eqb X) (btvbs bs)
          then t0
          else substA X U t0
        )
  | Let Rec bs t0 =>
      if existsb (eqb X) (btvbs bs)
        then
          Let Rec bs t0
        else
          Let Rec (@substA_br' substA_b X U bs) (substA X U t0)
  | Var y =>
      Var y
  | TyAbs bX K t0 =>
      if X =? bX
        then TyAbs bX K t0
        else TyAbs bX K (substA X U t0)
  | LamAbs bx T t0 =>
      LamAbs bx (substituteT X U T) (substA X U t0)
  | Apply t1 t2 =>
      Apply (substA X U t1) (substA X U t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | TyInst t0 T =>
      TyInst (substA X U t0) (substituteT X U T)
  | Error T =>
      Error (substituteT X U T)
  | IWrap F T t0 =>
      IWrap (substituteT X U F) (substituteT X U T) (substA X U t0)
  | Unwrap t0 =>
      Unwrap (substA X U t0)
  | Constr i ts =>
      Constr i (map (substA X U) ts)
  | Case t ts =>
      Case (substA X U t) (map (substA X U) ts)
  end

with substA_b (X : string) (U : Ty) (b : Binding) {struct b} : Binding :=
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y (substituteT X U T)) (substA X U tb)
  | TypeBind tvd T =>
      TypeBind tvd (substituteT X U T)
  | DatatypeBind (Datatype tvd YKs matchFunc cs) =>
      DatatypeBind (Datatype tvd YKs matchFunc (substA_cs X U cs))
  end.

Definition substA_bnr X U bs := @substA_bnr' substA_b X U bs.
Definition substA_br X U bs := @substA_br' substA_b X U bs.

Notation "'[[' U '/' X ']' t" := (substA X U t) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][b]' b" := (substA_b X U b) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][bnr]' bs" := (substA_bnr X U bs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][br]' bs" := (substA_br X U bs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][cs]' cs" := (substA_cs X U cs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][c]' c" := (substA_c X U c) (in custom plutus_term at level 20, X constr).


(** Multi-substitutions of types in type annotations *)
Fixpoint msubstA (ss : list (string * Ty)) (t : Term) : Term :=
  match ss with
  | nil => t
  | (X, U) :: ss' => msubstA ss' <{ [[U / X] t }>
  end.

Fixpoint msubstA_b (ss : list (string * Ty)) (b : Binding) : Binding :=
  match ss with
  | nil => b
  | (X, U) :: ss' => msubstA_b ss' <{ [[U / X][b] b }>
  end.

Fixpoint msubstA_bnr (ss : list (string * Ty)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_bnr ss' <{ [[U / X][bnr] bs }>
  end.

Fixpoint msubstA_br (ss : list (string * Ty)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_br ss' <{ [[U / X][br] bs }>
  end.

Fixpoint msubstA_cs (ss : list (string * Ty)) (cs : list VDecl) : list VDecl :=
  match ss with
  | nil => cs
  | (X, U) :: ss' => msubstA_cs ss' <{ [[U / X][cs] cs}>
  end.

Notation "'/[[' ss '/]' t" := (msubstA ss t) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][b]' b" := (msubstA_b ss b) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][bnr]' bs" := (msubstA_bnr ss bs) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][cs]' cs" := (msubstA_cs ss cs) (in custom plutus_term at level 20, ss constr).

