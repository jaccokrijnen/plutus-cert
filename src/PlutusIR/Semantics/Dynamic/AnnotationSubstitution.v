Require Import PlutusCert.PlutusIR.
Import PlutusNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** Substitution of types in type annotations *)

Section SubstABindings.
  Context {substAb : string -> ty -> binding -> binding}.

  Fixpoint substA_bnr' (X : string) (U : ty) (bs : list binding) : list binding :=
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

  Fixpoint substA_br' (X : string) (U : ty) (bs : list binding) : list binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        substAb X U b :: substA_br' X U bs'
    end.

End SubstABindings.

Section SubstAConstructors.

  Definition substA_c (X : string) (U : ty) (c : vdecl) : vdecl :=
    match c with
    | VarDecl bx T =>
        VarDecl bx (substituteT X U T)
    end.

  Definition substA_cs (X : string) (U : ty) (cs : list vdecl) : list vdecl :=
    map (substA_c X U) cs.

End SubstAConstructors.


Fixpoint substA (X : string) (U : ty) (t : term) {struct t} : term :=
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
  | Constr T i ts =>
      Constr (substituteT X U T) i (map (substA X U) ts)
  | Case T t ts =>
      Case (substituteT X U T) (substA X U t) (map (substA X U) ts)
  end

with substA_b (X : string) (U : ty) (b : binding) {struct b} : binding :=
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

Notation "':[' X ':=' U ']' t" := (substA X U t) (in custom plutus_term at level 20, X constr).
Notation "':[' X ':=' U ']b' b" := (substA_b X U b) (in custom plutus_term at level 20, X constr).
Notation "':[' X ':=' U ']bnr' bs" := (substA_bnr X U bs) (in custom plutus_term at level 20, X constr).
Notation "':[' X ':=' U ']br' bs" := (substA_br X U bs) (in custom plutus_term at level 20, X constr).
Notation "':[' X ':=' U ']cs' cs" := (substA_cs X U cs) (in custom plutus_term at level 20, X constr).
Notation "':[' X ':=' U ']c' c" := (substA_c X U c) (in custom plutus_term at level 20, X constr).


(** Multi-substitutions of types in type annotations *)
Fixpoint msubstA (ss : list (string * ty)) (t : term) : term :=
  match ss with
  | nil => t
  | (X, U) :: ss' => msubstA ss' <{ :[X := U] t }>
  end.

Fixpoint msubstA_b (ss : list (string * ty)) (b : binding) : binding :=
  match ss with
  | nil => b
  | (X, U) :: ss' => msubstA_b ss' <{ :[X := U]b b }>
  end.

Fixpoint msubstA_bnr (ss : list (string * ty)) (bs : list binding) : list binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_bnr ss' <{ :[X := U]bnr bs }>
  end.

Fixpoint msubstA_br (ss : list (string * ty)) (bs : list binding) : list binding :=
  match ss with
  | nil => bs
  | (X, U) :: ss' => msubstA_br ss' <{ :[X := U]br bs }>
  end.

Fixpoint msubstA_cs (ss : list (string * ty)) (cs : list vdecl) : list vdecl :=
  match ss with
  | nil => cs
  | (X, U) :: ss' => msubstA_cs ss' <{ :[X := U]cs cs}>
  end.

Notation "':[' ss ']*' t" := (msubstA ss t) (in custom plutus_term at level 20, ss constr).
Notation "':[' ss ']*b' b" := (msubstA_b ss b) (in custom plutus_term at level 20, ss constr).
Notation "':[' ss ']*bnr' bs" := (msubstA_bnr ss bs) (in custom plutus_term at level 20, ss constr).
Notation "':[' ss ']*cs' cs" := (msubstA_cs ss cs) (in custom plutus_term at level 20, ss constr).

