From PlutusCert Require Import
  Language.PlutusIR
  .
Import NamedTerm.

Section LetNonStrict.
Context
  {var tyvar : Set}
  (var_eqb : var -> var -> bool).

Notation term' := (term var tyvar var tyvar).

(*

Polymorphic Inductive Desugar : term' -> term' -> Type :=
  | DesugarVar       : forall v w,
      Desugar (Var v) (Var w)

  | DesugarLetNonRec : forall bs bs' t t',
      DesugarBindingsNonRec bs bs' ->
      Desugar t t' ->
      Desugar (Let NonRec bs t) (Let NonRec bs' t')

  | DesugarLetRec    : forall bs bs' t t',
      DesugarBindingsRec bs bs' ->
      Desugar t t' ->
      Desugar (Let Rec bs t) (Let Rec bs' t')

  (*
     | DesugarCong      : forall env t t', Cong (Desugar env) t t' -> Desugar env t t'

     Using Cong is not sound when shadowing can occur: using Cong includes
     Lets that don't extend the rename env. That means that if a shadowing
     binding is not included, its occurences may be renamed to the original
     binder's renaming. This should not be a problem when all variables are
     globally unique.

     Using Cong is also not nice, it should only capture the Term constructors
     that were not used in the "interesting" rules above. A search should never
     use the Cong case for Let, for example.

     So we write out all other cases by hand...
  *)

  | DesugarTyAbs : forall ty k t t',
      Desugar t t' ->
      Desugar (TyAbs ty k t) (TyAbs ty k t')
  | DesugarLamAbs : forall v ty t t',
      Desugar t t' ->
      Desugar (LamAbs v ty t) (LamAbs v ty t')
  | DesugarApply : forall t1 t2 t1' t2',
      Desugar t1 t1' ->
      Desugar t2 t2' ->
      Desugar (Apply t1 t2) (Apply t1' t2')
  | DesugarConstant : forall c,
      Desugar (Constant c) (Constant c)
  | DesugarBuiltin : forall f,
      Desugar (Builtin f) (Builtin f)
  | DesugarTyInst : forall t t' ty,
      Desugar t t' ->
      Desugar (TyInst t ty) (TyInst t' ty)
  | DesugarError : forall ty,
      Desugar (Error ty) (Error ty)
  | DesugarIWrap : forall ty1 ty2 t t',
      Desugar t t' ->
      Desugar (IWrap ty1 ty2 t) (IWrap ty1 ty2 t')
  | DesugarUnwrap : forall t t',
      Desugar t t' ->
      Desugar (Unwrap t) (Unwrap t')
(*
Non-recursive: the environment can be extended and passed down
*)
with DesugarBindingsNonRec (env : environment): (* environment passed down (accumulating param) *)
  environment ->         (* resulting environment, used for the let-body *)
  list (binding var tyvar var tyvar) -> (* bindings before translation *)
  list (binding var tyvar var tyvar) -> (* bindings after translation*)
  Type :=
  | NonRecCons : forall env' env_up b b' bs bs',
      DesugarBinding env  env_up b b' ->
      DesugarBindingsNonRec (env_up ++ env) env'       bs         bs' ->
      DesugarBindingsNonRec            env  env' (b :: bs) (b' :: bs')
  | NonRecNil  : DesugarBindingsNonRec env env nil nil

(*
Recursive: the inherited environment already contains the bindings in this group,
so it does not have to be extended
*)
with DesugarBindingsRec (env : environment): (* parametrized by the environment*)
  environment ->         (* resulting environment, used for the let-body AND env parameter (see Desugar_LetRec)*)
  list (binding var tyvar var tyvar) -> (* bindings before translation *)
  list (binding var tyvar var tyvar) -> (* bindings after translation*)
  Type :=
  | RecCons : forall env_b env_bs b b' bs bs',
      DesugarBinding     env  env_b            b         b'         ->
      DesugarBindingsRec env           env_bs        bs         bs' ->
      DesugarBindingsRec env (env_b ++ env_bs) (b :: bs) (b' :: bs')
  | RecNil  : DesugarBindingsRec env nil nil nil

with DesugarBinding (env : environment) :
  environment -> (* rename results for this binding *)
  binding var tyvar var tyvar ->
  binding var tyvar var tyvar -> Type :=

  | BindEq     : forall s v t t' ty,
      Desugar env t t' ->
      DesugarBinding env [(v, Unchanged)]
        (TermBind s (VarDecl v ty) t)
        (TermBind s (VarDecl v ty) t')

  | BindDesugar : forall s v w t t' ty,
      v <> w ->
      ~ (In w (freeVars var_eqb t)) ->
      Desugar env t t' ->
      DesugarBinding env [(v, DesugardTo w)]
        (TermBind s (VarDecl v ty) t )
        (TermBind s (VarDecl w ty) t')

  | DataEq : forall d d' env_up,
      Desugar_dtdecl env env_up d d' ->
      DesugarBinding env env_up
        (DatatypeBind d)
        (DatatypeBind d')

  | TypeEq : forall t ty,
      DesugarBinding env nil
        (TypeBind t ty)
        (TypeBind t ty)

with Desugar_dtdecl (env : environment) :
  environment ->
  dtdecl' -> dtdecl' -> Type :=
    | Desugar_Datatype : forall var_res matchf matchf' cs_res cs cs' tv tvs ,
      Desugar_var env var_res matchf matchf' ->
      Desugar_constrs env cs_res cs cs' ->
      Desugar_dtdecl env (var_res :: cs_res)
        (Datatype tv tvs matchf  cs)
        (Datatype tv tvs matchf' cs')

with Desugar_var (env : environment) : (var * rename_result) -> var -> var -> Type :=
  | VarEq  : forall v,
      Desugar_var env (v, Unchanged) v v
  | VarNeq : forall v v',
      v <> v' ->
      Desugar_var env (v, DesugardTo v') v v'

with Desugar_constrs (env : environment) :
  environment ->
  list constr' ->
  list constr' ->
  Type :=
  | Desugar_constrs_cons : forall c cs c' cs' c_res env',
      Desugar_constr env c_res c c' ->
      Desugar_constrs env env' cs cs' ->
      Desugar_constrs env (c_res :: env') (c :: cs) (c' :: cs')

  | Desugar_constrs_nil  : Desugar_constrs env nil nil nil

with Desugar_constr (env : environment) :
  (var * rename_result) ->
  constr' ->
  constr' ->
  Type :=
  | Desugar_Constructor : forall res v v' ty arity,
      Desugar_var env res v v' ->
      Desugar_constr
        env
        res
        (Constructor (VarDecl v ty) arity)
        (Constructor (VarDecl v' ty) arity)
  .

*)
End LetNonStrict.
