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

Import NamedTerm.

Module Ty.

  Inductive appears_bound_in (X: tyname) : Ty -> Prop :=
    | ABI_TyFun1 : forall T1 T2,
        appears_bound_in X T1 ->
        appears_bound_in X (Ty_Fun T1 T2)
    | ABI_TyFun2 : forall T1 T2,
        appears_bound_in X T2 ->
        appears_bound_in X (Ty_Fun T1 T2)
    | ABI_TyIFix1 : forall F T,
        appears_bound_in X F ->
        appears_bound_in X (Ty_IFix F T)
    | ABI_TyIFix2 : forall F T,
        appears_bound_in X T ->
        appears_bound_in X (Ty_IFix F T)
    | ABI_TyForall1 : forall K T,
        appears_bound_in X (Ty_Forall X K T)
    | ABI_TyForall2 : forall Y K T,
        X <> Y ->
        appears_bound_in Y T ->
        appears_bound_in X (Ty_Forall Y K T)
    | ABI_TyLam1 : forall K T,
        appears_bound_in X (Ty_Lam X K T)
    | ABI_TyLam2 : forall Y K T,
        X <> Y ->
        appears_bound_in Y T ->
        appears_bound_in X (Ty_Lam Y K T)
    | ABI_TyApp1 : forall T1 T2,
        appears_bound_in X T1 ->
        appears_bound_in X (Ty_App T1 T2)
    | ABI_TyApp2 : forall T1 T2,  
        appears_bound_in X T2 ->
        appears_bound_in X (Ty_App T1 T2).

End Ty.

Module Term.

  Definition bv_constructor (c : constructor) : string :=
    match c with
    | Constructor (VarDecl x _) _ => x
    end.

  Inductive appears_bound_in (x : name) : Term -> Prop :=
    | ABI_LamAbs1 : forall T t,
        appears_bound_in x (LamAbs x T t)
    | ABI_LamAbs2 : forall y T t,
        x <> y ->
        appears_bound_in x t ->
        appears_bound_in x (LamAbs y T t)
    | ABI_Apply1 : forall t1 t2,
        appears_bound_in x t1 ->
        appears_bound_in x (Apply t1 t2)
    | ABI_Apply2 : forall t1 t2,
        appears_bound_in x t2 ->
        appears_bound_in x (Apply t1 t2)
    | ABI_TyAbs : forall X K t,
        appears_bound_in x t ->
        appears_bound_in x (TyAbs X K t)
    | ABI_TyInst : forall t T,
        appears_bound_in x t ->
        appears_bound_in x (TyInst t T)
    | ABI_IWrap : forall F T t,
        appears_bound_in x t ->
        appears_bound_in x (IWrap F T t)
    | ABI_Unwrap : forall t,
        appears_bound_in x t ->
        appears_bound_in x (Unwrap t)
    | ABI_Let_Nil : forall recty t0,
        appears_bound_in x t0 ->
        appears_bound_in x (Let recty nil t0)
    | ABI_Let_Cons : forall recty b bs t0,
        appears_bound_in x (Let recty bs t0) ->
        appears_bound_in x (Let recty (b :: bs) t0)
    | ABI_Let_TermBind1 : forall recty stricty T t bs t0,
        appears_bound_in x (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
    | ABI_Let_TermBind2 : forall recty stricty y T t bs t0,
        appears_bound_in x t ->
        appears_bound_in x (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
    | ABI_Let_DatatypeBind : forall recty XK YKs mfunc cs t0 bs,
        In x (mfunc :: map bv_constructor cs) ->
        appears_bound_in x (Let recty (DatatypeBind (Datatype XK YKs mfunc cs) :: bs) t0) 
    .

End Term.

Module Annotation.

  Inductive appears_bound_in (X : tyname) : Term -> Prop :=
    | ABI_LamAbs1 : forall x T t,
        Ty.appears_bound_in X T ->
        appears_bound_in X (LamAbs x T t)
    | ABI_LamAbs : forall x T t,
        appears_bound_in X t ->
        appears_bound_in X (LamAbs x T t)
    | ABI_Apply1 : forall t1 t2,
        appears_bound_in X t1 ->
        appears_bound_in X (Apply t1 t2)
    | ABI_Apply2 : forall t1 t2,
        appears_bound_in X t2 ->
        appears_bound_in X (Apply t1 t2)
    | ABI_TyAbs1 : forall K t,
        appears_bound_in X (TyAbs X K t)
    | ABI_TyAbs2 : forall Y K t,
        X <> Y ->
        appears_bound_in X t ->
        appears_bound_in X (TyAbs Y K t)
    | ABI_TyInst1 : forall t T,
        appears_bound_in X t ->
        appears_bound_in X (TyInst t T)
    | ABI_TyInst2 : forall t T,
        Ty.appears_bound_in X T ->
        appears_bound_in X (TyInst t T)
    | ABI_IWrap1 : forall F T t,
        Ty.appears_bound_in X F ->
        appears_bound_in X (IWrap F T t)
    | ABI_IWrap2 : forall F T t,
        Ty.appears_bound_in X T ->
        appears_bound_in X (IWrap F T t)
    | ABI_IWrap3 : forall F T t,
        appears_bound_in X t ->
        appears_bound_in X (IWrap F T t)
    | ABI_Unwrap : forall t,
        appears_bound_in X t ->
        appears_bound_in X (Unwrap t)
    | ABI_Error : forall T,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Error T)
    | ABI_Let_Nil : forall recty t0,
        appears_bound_in X t0 ->
        appears_bound_in X (Let recty nil t0)
    | ABI_Let_Cons : forall recty b bs t0,
        appears_bound_in X (Let recty bs t0) ->
        appears_bound_in X (Let recty (b :: bs) t0)
    | ABI_Let_TermBind1 : forall recty stricty x T t bs t0,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Let recty (TermBind stricty (VarDecl x T) t :: bs) t0)
    | ABI_Let_TermBind2 : forall recty stricty y T t bs t0,
        appears_bound_in X t ->
        appears_bound_in X (Let recty (TermBind stricty (VarDecl y T) t :: bs) t0)
    | ABI_Let_TypeBind1 : forall recty K T bs t0,
        appears_bound_in X (Let recty (TypeBind (TyVarDecl X K) T :: bs) t0)
    | ABI_Let_TypeBind2 : forall recty Y K T bs t0,
        Ty.appears_bound_in X T ->
        appears_bound_in X (Let recty (TypeBind (TyVarDecl Y K) T :: bs) t0)
    | ABI_Let_DatatypeBind : forall recty K YKs mfunc cs t0 bs,
        appears_bound_in X (Let recty (DatatypeBind (Datatype (TyVarDecl X K) YKs mfunc cs) :: bs) t0) 
    .

End Annotation.

#[export] Hint Constructors 
  Ty.appears_bound_in 
  Term.appears_bound_in
  Annotation.appears_bound_in
  : core.


(** Retrieve bound term variable bindings *)

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
  
(** Retrieve bound type variable bindings *)

Definition btvb (b : NamedTerm.Binding) : list tyname :=
  match b with
  | TermBind _ (VarDecl x _) _ => nil
  | TypeBind (TyVarDecl X _) _ => cons X nil
  | DatatypeBind (Datatype (TyVarDecl X _) YKs matchFunc cs) => cons X nil
  end.

Definition btvbs (bs : list NamedTerm.Binding) : list tyname := List.concat (map btvb bs).

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
