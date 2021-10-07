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
  Language.PlutusIR.Folds.


Set Polymorphic Universes.

Fixpoint bv_term {v v'} (t : term v v' v v') : list v :=
  match t with
  | Let _ bs t  => concat (map bv_binding bs)
  | Var _       => []
  | TyAbs _ _ t => bv_term t
  | LamAbs v _ t => [v] ++ bv_term t
  | Apply s t  => bv_term s ++ bv_term t
  | Constant _ => []
  | Builtin _  => []
  | TyInst t _ => bv_term t
  | Error _   => []
  | IWrap _ _ t => bv_term t
  | Unwrap t => bv_term t
  | ExtBuiltin f args => concat (map bv_term args)
  end
with bv_binding {v v'} (b : binding v v' v v') : list v:=
  match b with
  | TermBind _ (VarDecl v _) t => [v] ++ bv_term t
  | TypeBind _ _   => []
  | DatatypeBind _ => []
  end
.

Section UniqueVars.
  Context (name tyname : Set).

  Inductive UniqueVars : term name tyname name tyname -> Type :=
    | UV_Let : forall {r bs t}, ForallT (UniqueVars_binding) bs -> UniqueVars t -> UniqueVars (Let r bs t)
    | UV_Var : forall v, UniqueVars (Var v)
    | UV_TyAbs : forall v k t, UniqueVars t -> UniqueVars (TyAbs v k t)
    | UV_LamAbs : forall v ty t, ~(In v (bv_term t)) -> UniqueVars t -> UniqueVars (LamAbs v ty t)
    | UV_Apply : forall s t, UniqueVars s -> UniqueVars t -> UniqueVars (Apply s t)
    | UV_Constant : forall c, UniqueVars (Constant c)
    | UV_Builtin : forall f, UniqueVars (Builtin f)
    | UV_TyInst : forall t ty, UniqueVars t -> UniqueVars (TyInst t ty)
    | UV_Error : forall ty, UniqueVars (Error ty)
    | UV_IWrap : forall ty1 ty2 t, UniqueVars t -> UniqueVars (IWrap ty1 ty2 t)
    | UV_Unwrap : forall t, UniqueVars t -> UniqueVars (Unwrap t)
    | UV_ExtBuiltin : forall f args, ForallT (UniqueVars) args -> UniqueVars (ExtBuiltin f args)

    with UniqueVars_binding : binding name tyname name tyname -> Type :=
    | UV_TermBind : forall s v t ty, ~(In v (bv_term t)) -> UniqueVars t -> UniqueVars_binding (TermBind s (VarDecl v ty) t)
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
