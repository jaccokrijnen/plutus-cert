Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

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