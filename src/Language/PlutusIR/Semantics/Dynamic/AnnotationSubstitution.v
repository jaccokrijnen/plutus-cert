Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import PlutusCert.Language.PlutusIR.Analysis.BoundVars.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** Substitution of types in type annotations *)

Section SubstABindings.
  Context {substAb : tyname -> Ty -> Binding -> Binding}.

  Fixpoint substituteA_bindings_nonrec (X : tyname) (U : Ty) (bs : list Binding) : list Binding :=
    match bs with
    | nil => 
        nil
    | b :: bs' => 
        if existsb (eqb X) (btvb b)
          then
            substAb X U b :: bs'
          else
            substAb X U b :: substituteA_bindings_nonrec X U bs'
    end.

  Fixpoint substituteA_bindings_rec (X : tyname) (U : Ty) (bs : list Binding) : list Binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        substAb X U b :: substituteA_bindings_rec X U bs'
    end.

End SubstABindings.

Section SubstAConstructors.

  Definition substituteA_constructor (X : tyname) (U : Ty) (c : constructor) : constructor :=
    match c with
    | Constructor (VarDecl bx T) ar =>
        Constructor (VarDecl bx (substituteT X U T)) ar
    end.

  Definition substituteA_constructors (X : tyname) (U : Ty) (cs : list constructor) : list constructor :=
    map (substituteA_constructor X U) cs.

End SubstAConstructors.


Fixpoint substituteA (X : tyname) (U : Ty) (t : Term) {struct t} : Term :=
  match t with
  | Let NonRec bs t0 =>
      Let NonRec (@substituteA_bindings_nonrec substituteA_binding X U bs)
        (if existsb (eqb X) (btvbs bs) 
          then t0
          else substituteA X U t0
        ) 
  | Let Rec bs t0 =>
      if existsb (eqb X) (btvbs bs) 
        then 
          Let Rec bs t0
        else
          Let Rec (@substituteA_bindings_rec substituteA_binding X U bs) (substituteA X U t0)
  | Var y => 
      Var y
  | TyAbs bX K t0 =>
      if X =? bX
        then TyAbs bX K t0
        else TyAbs bX K (substituteA X U t0)
  | LamAbs bx T t0 =>
      LamAbs bx (substituteT X U T) (substituteA X U t0)
  | Apply t1 t2 =>
      Apply (substituteA X U t1) (substituteA X U t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | TyInst t0 T =>
      TyInst (substituteA X U t0) (substituteT X U T)
  | Error T =>
      Error (substituteT X U T)
  | IWrap F T t0 =>
      IWrap (substituteT X U F) (substituteT X U T) (substituteA X U t0)
  | Unwrap t0 =>
      Unwrap (substituteA X U t0)
  end

with substituteA_binding (X : tyname) (U : Ty) (b : Binding) {struct b} : Binding :=
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y (substituteT X U T)) (substituteA X U tb)
  | TypeBind tvd T => 
      TypeBind tvd (substituteT X U T)
  | DatatypeBind (Datatype tvd YKs matchFunc cs) =>
      DatatypeBind (Datatype tvd YKs matchFunc (substituteA_constructors X U cs))
  end.

Notation "'[[' U '/' X ']' t" := (substituteA X U t) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][b]' b" := (substituteA_binding X U b) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][bnr]' bs" := (@substituteA_bindings_nonrec substituteA_binding X U bs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][br]' bs" := (@substituteA_bindings_rec substituteA_binding X U bs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][cs]' cs" := (substituteA_constructors X U cs) (in custom plutus_term at level 20, X constr).
Notation "'[[' U '/' X '][c]' c" := (substituteA_constructor X U c) (in custom plutus_term at level 20, X constr).

(** Multi-substitutions of types in type annotations *)
Fixpoint msubstA_term (ss : list (tyname * Ty)) (t : Term) : Term :=
  match ss with
  | nil => t
  | (X, U) :: ss' => msubstA_term ss' <{ [[U / X] t }>
  end.

Fixpoint msubstA_binding (ss : list (tyname * Ty)) (b : Binding) : Binding :=
  match ss with
  | nil => b
  | (X, U) :: ss' => msubstA_binding ss' <{ [[U / X][b] b }>
  end.

Fixpoint msubstA_bindings_nonrec (ss : list (tyname * Ty)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_bindings_nonrec ss' <{ [[U / X][bnr] bs }>
  end.

Fixpoint msubstA_bindings_rec (ss : list (tyname * Ty)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_bindings_rec ss' <{ [[U / X][br] bs }>
  end.

Fixpoint msubstA_constructors (ss : list (tyname * Ty)) (cs : list constructor) : list constructor :=
  match ss with
  | nil => cs
  | (X, U) :: ss' => msubstA_constructors ss' <{ [[U / X][cs] cs}>
  end.

Notation "'/[[' ss '/]' t" := (msubstA_term ss t) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][b]' b" := (msubstA_binding ss b) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][bnr]' bs" := (msubstA_bindings_nonrec ss bs) (in custom plutus_term at level 20, ss constr).
Notation "'/[[' ss '/][cs]' cs" := (msubstA_constructors ss cs) (in custom plutus_term at level 20, ss constr).
  
