From Coq Require Import
  String
  List
  .
From PlutusCert Require Import
  Util
  Language.PlutusIR
  Transform.Congruence
  Analysis.FreeVars
  .


Section Rename.
Context
  {var : Set}
  (var_eqb : var -> var -> bool).

(* Alpha renaming of variables *)
Polymorphic Inductive Rename env : term var -> term var -> Type :=

  | RenameVar       : forall v w,
      In (v, w) env ->
      Rename env (Var v) (Var w)

  | RenameLetNonRec : forall bs bs' env' t t',
      RenameBindingsNonRec env env' bs bs' ->
      Rename env' t t' ->
      Rename env (Let NonRec bs t) (Let NonRec bs' t')

  | RenameLetRec    : forall bs bs' env' t t',
      RenameBindingsRec env env' bs bs' ->
      Rename env' t t' ->
      Rename env (Let Rec bs t) (Let Rec bs' t')

  (*
     | RenameCong      : forall env t t', Cong (Rename env) t t' -> Rename env t t'

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

  | RenameTyAbs : forall ty k t t',
      Rename env t t' ->
      Rename env (TyAbs ty k t) (TyAbs ty k t')
  | RenameLamAbs : forall v ty t t',
      Rename env t t' ->
      Rename env (LamAbs v ty t) (LamAbs v ty t')
  | RenameApply : forall t1 t2 t1' t2',
      Rename env t1 t1' ->
      Rename env t2 t2' ->
      Rename env (Apply t1 t2) (Apply t1' t2')
  | RenameConstant : forall c,
      Rename env (Constant c) (Constant c)
  | RenameBuiltin : forall f,
      Rename env (Builtin f) (Builtin f)
  | RenameTyInst : forall t t' ty,
      Rename env t t' ->
      Rename env (TyInst t ty) (TyInst t' ty)
  | RenameError : forall ty,
      Rename env (Error ty) (Error ty)
  | RenameIWrap : forall ty1 ty2 t t',
      Rename env t t' ->
      Rename env (IWrap ty1 ty2 t) (IWrap ty1 ty2 t')
  | RenameUnwrap : forall t t',
      Rename env t t' ->
      Rename env (Unwrap t) (Unwrap t')

with RenameBindingsNonRec env :
  list (var * var) ->
  list (binding var) ->
  list (binding var) ->
  Type :=
  | NonRecCons : forall env' env'' b b' bs bs',
      RenameBindingNonRec  env  env'   b         b'        ->
      RenameBindingsNonRec env' env''       bs         bs' ->
      RenameBindingsNonRec env  env'' (b :: bs) (b' :: bs')
  | NonRecNil  : RenameBindingsNonRec env env nil nil

with RenameBindingNonRec env :
  list (var * var) -> (* The extended environment *)
  binding var ->
  binding var -> Type :=
  | BindEq     : forall s v t t',
      Rename env t t' -> RenameBindingNonRec env env (TermBind s v t) (TermBind s v t')

  | BindRename : forall s v w t t' ty,
      v <> w ->
      ~ (In w (freeVars var_eqb t)) -> (* w cannot occur free in t, otherwise the new binding would capture it *)
      Rename env t t' -> RenameBindingNonRec env ((v, w) :: env) (TermBind s (VarDecl v ty) t) (TermBind s (VarDecl w ty) t')

  | TypeEq : forall t ty, RenameBindingNonRec env env (TypeBind t ty) (TypeBind t ty)
  | DataEq : forall d , RenameBindingNonRec env env (DatatypeBind d) (DatatypeBind d)

with RenameBindingsRec env :
  list (var * var) ->
  list (binding var) ->
  list (binding var) ->
  Type :=
  (* TODO: recursive bindings, different scoping *)
  .

End Rename.
Definition Rename_string := Rename (var := string) String.eqb nil.

(* TODO: recursive bindings, different scoping *)
(*
Polymorphic Inductive RenameBindingRec {n} env :
  list (n * n) -> (* The extended environment *)
  binding n ->
  binding n ->
  Type :=
  (*
  | RenameTerm :
  | RenameType :
  | RenameData :
  *)
  .
  *)
