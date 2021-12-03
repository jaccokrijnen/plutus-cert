From Coq Require Import
  Strings.String
  Lists.List
  Arith.PeanoNat
  Strings.Ascii.

Import ListNotations.
Local Open Scope string_scope.

From PlutusCert Require Import
  Util
  Language.PlutusIR
  Language.PlutusIR.Folds
  FreeVars.


Section BoundVars.
  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    .

Notation term'    := (term var tyvar var tyvar).
Notation binding' := (binding var tyvar var tyvar).

Fixpoint bound_vars (t : term') : list var :=
 match t with
   | Let rec bs t => bound_vars_bindings bs ++ bound_vars t
   | (LamAbs n ty t)   => n :: (bound_vars t)
   | (Var n)           => []
   | (TyAbs n k t)     => bound_vars t
   | (Apply s t)       => bound_vars s ++ bound_vars t
   | (TyInst t ty)     => bound_vars t
   | (IWrap ty1 ty2 t) => bound_vars t
   | (Unwrap t)        => bound_vars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   end.

End BoundVars.

Section UniqueVars.
  Context (name tyname : Set).

  Inductive UniqueVars : term name tyname name tyname -> Type :=
    | UV_Let : forall {r bs t}, ForallT (UniqueVars_binding) bs -> UniqueVars t -> UniqueVars (Let r bs t)
    | UV_Var : forall v, UniqueVars (Var v)
    | UV_TyAbs : forall v k t, UniqueVars t -> UniqueVars (TyAbs v k t)
    | UV_LamAbs : forall v ty t, ~(In v (bound_vars t)) -> UniqueVars t -> UniqueVars (LamAbs v ty t)
    | UV_Apply : forall s t, UniqueVars s -> UniqueVars t -> UniqueVars (Apply s t)
    | UV_Constant : forall c, UniqueVars (Constant c)
    | UV_Builtin : forall f, UniqueVars (Builtin f)
    | UV_TyInst : forall t ty, UniqueVars t -> UniqueVars (TyInst t ty)
    | UV_Error : forall ty, UniqueVars (Error ty)
    | UV_IWrap : forall ty1 ty2 t, UniqueVars t -> UniqueVars (IWrap ty1 ty2 t)
    | UV_Unwrap : forall t, UniqueVars t -> UniqueVars (Unwrap t)
    
    with UniqueVars_binding : binding name tyname name tyname -> Type :=
    | UV_TermBind : forall s v t ty, ~(In v (bound_vars t)) -> UniqueVars t -> UniqueVars_binding (TermBind s (VarDecl v ty) t)
    | UV_TypeBind : forall tvd ty, UniqueVars_binding (TypeBind tvd ty)
    | UV_DatatypeBind : forall dtd, UniqueVars_binding (DatatypeBind dtd)
    .

End UniqueVars.

Inductive decide {a : Type} (P : a -> Type) (x : a) :=
  | dec_False : notT (P x) -> decide P x
  | dec_True  : P x        -> decide P x
  .
Hint Constructors decide : core.

Definition dec_all a P (xs : list a) : ForallT (decide P) xs -> decide (ForallT P) xs.
Proof.
Admitted.

Definition check_unique : forall v v' t, decide (UniqueVars v v') t.
Proof.
Admitted.
