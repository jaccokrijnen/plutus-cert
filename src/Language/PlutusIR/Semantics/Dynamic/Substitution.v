Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Import Coq.Lists.List.
Import Coq.Strings.String.

Local Open Scope string_scope.



(** Substitution of terms *)

Definition bvc (c : NamedTerm.constructor) : string :=
  match c with
  | Constructor (VarDecl x _) _ => x
  end.

Definition bvb (b : NamedTerm.Binding) : list string :=
  match b with
  | TermBind _ (VarDecl x _) _ => cons x nil
  | TypeBind (TyVarDecl X _) _ => nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => matchFunc :: (rev (map bvc cs))
  end.

Definition bvbs (bs : list NamedTerm.Binding) : list string := List.concat (map bvb bs).



Section SubstBindings.
  Context {substb : name -> Term -> Binding -> Binding}.

  Fixpoint substitute_bindings_nonrec (x : name) (s : Term) (bs : list Binding) : list Binding :=
    match bs with
    | nil => 
        nil
    | b :: bs' => 
        if existsb (eqb x) (bvb b)
          then
            substb x s b :: bs'
          else
            substb x s b :: substitute_bindings_nonrec x s bs'
    end.

  Fixpoint substitute_bindings_rec (x : name) (s : Term) (bs : list Binding) : list Binding :=
    match bs with
    | nil =>
        nil
    | b :: bs' =>
        substb x s b :: substitute_bindings_rec x s bs'
    end.

End SubstBindings.

Fixpoint substitute (x : name) (s : Term) (t : Term) {struct t} : Term :=
  match t with
  | Let NonRec bs t0 =>
      Let NonRec (@substitute_bindings_nonrec substitute_binding x s bs)
        (if existsb (eqb x) (bvbs bs) 
          then t0
          else substitute x s t0
        ) 
  | Let Rec bs t0 =>
      if existsb (eqb x) (bvbs bs) 
        then 
          Let Rec bs t0
        else
          Let Rec (@substitute_bindings_rec substitute_binding x s bs) (substitute x s t0)
  | Var y => 
      if x =? y
        then s
        else Var y
  | TyAbs bX K t0 =>
      TyAbs bX K (substitute x s t0)
  | LamAbs bx T t0 =>
      if x =? bx
        then LamAbs bx T t0
        else LamAbs bx T (substitute x s t0)
  | Apply t1 t2 =>
      Apply (substitute x s t1) (substitute x s t2)
  | Constant u =>
      Constant u
  | Builtin d =>
      Builtin d
  | TyInst t0 T =>
      TyInst (substitute x s t0) T
  | Error T =>
      Error T
  | IWrap F T t0 =>
      IWrap F T (substitute x s t0)
  | Unwrap t0 =>
      Unwrap (substitute x s t0)
  end

with substitute_binding (x : name) (s : Term) (b : Binding) {struct b} : Binding :=
  match b with
  | TermBind stricty (VarDecl y T) tb =>
      TermBind stricty (VarDecl y T) (substitute x s tb)
  | _ => b
  end.

Notation "'[' s '/' x ']' t" := (substitute x s t) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][b]' b" := (substitute_binding x s b) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][bnr]' bs" := (@substitute_bindings_nonrec substitute_binding x s bs) (in custom plutus_term at level 20, x constr).
Notation "'[' s '/' x '][br]' bs" := (@substitute_bindings_rec substitute_binding x s bs) (in custom plutus_term at level 20, x constr).

(** Multi-substitutions of terms *)
Fixpoint msubst_term (ss : list (name * Term)) (t : Term) : Term :=
  match ss with
  | nil => t
  | (x, s) :: ss' => msubst_term ss' <{ [s / x] t }>
  end.

Fixpoint msubst_binding (ss : list (name * Term)) (b : Binding) : Binding :=
  match ss with
  | nil => b
  | (x, s) :: ss' => msubst_binding ss' <{ [s / x][b] b }>
  end.

Fixpoint msubst_bindings_nonrec (ss : list (name * Term)) (bs : list Binding) : list Binding :=
  match ss with
  | nil => bs
  | (x, s) :: ss' => msubst_bindings_nonrec ss' <{ [s / x][bnr] bs }>
  end.

Notation "'/[' ss '/]' t" := (msubst_term ss t) (in custom plutus_term at level 20, ss constr).
Notation "'/[' ss '/][b]' b" := (msubst_binding ss b) (in custom plutus_term at level 20, ss constr).
Notation "'/[' ss '/][bnr]' bs" := (msubst_bindings_nonrec ss bs) (in custom plutus_term at level 20, ss constr).
