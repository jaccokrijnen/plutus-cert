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
  {var tyvar : Set}
  (var_eqb : var -> var -> bool).

Inductive rename_result :=
  | RenamedTo : var -> rename_result
  | Unchanged : rename_result
  .

Notation dtdecl' := (dtdecl tyvar var tyvar).
Notation constr' := (constr tyvar var tyvar).
Notation environment := (list (var * rename_result)).

Import ListNotations.


Fixpoint lookupRR (env : environment) (x : var) : option rename_result :=
  match env with 
  | nil => None
  | (y, rr) :: env' => if var_eqb x y then Datatypes.Some rr else lookupRR env' x
  end.

Definition rename_result_eqb (rr1 rr2 : rename_result) :=
  match rr1, rr2 with
  | RenamedTo y1, RenamedTo y2 => var_eqb y1 y2
  | _, _ => true
  end.

Fixpoint lookupV (env : environment) (rr : rename_result) : option var :=
  match env with
  | nil => None
  | (y, rr') :: env' => if rename_result_eqb rr rr' then Datatypes.Some y else lookupV env' rr
  end.

(* Alpha renaming of term variables *)
Polymorphic Inductive Rename : environment -> term var tyvar var tyvar -> term var tyvar var tyvar -> Type :=
  | RenameVar       : forall env v w,
      lookupRR env v = Datatypes.Some (RenamedTo w) ->
      Rename env (Var v) (Var w)

  | RenameVarEq     : forall env v,
      lookupRR env v = Datatypes.Some Unchanged ->
      Rename env (Var v) (Var v)

  | RenameLetNonRec : forall env bs bs' env' t t',
      RenameBindingsNonRec env env' bs bs' ->
      Rename env' t t' ->
      Rename env (Let NonRec bs t) (Let NonRec bs' t')

  | RenameLetRec    : forall env bs bs' env' t t',
      RenameBindingsRec env env' bs bs' ->
      Rename env' t t' ->
      Rename env (Let Rec bs t) (Let Rec bs' t')

  | RenameLamAbsRename : forall env v w ty t t',
      v <> w ->
      ~ (In w (free_vars var_eqb t)) ->
      ~ (In (RenamedTo w) (map snd env)) ->
      lookupV env (RenamedTo w) = None ->
      Rename ((v, RenamedTo w) :: env) t t' ->
      Rename env (LamAbs v ty t) (LamAbs w ty t')
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

  | RenameTyAbs : forall env ty k t t',
      Rename env t t' ->
      Rename env (TyAbs ty k t) (TyAbs ty k t')
  | RenameLamAbsEq : forall env v ty t t',
      Rename env t t' ->
      Rename env (LamAbs v ty t) (LamAbs v ty t')
  | RenameApply : forall env t1 t2 t1' t2',
      Rename env t1 t1' ->
      Rename env t2 t2' ->
      Rename env (Apply t1 t2) (Apply t1' t2')
  | RenameConstant : forall env c,
      Rename env (Constant c) (Constant c)
  | RenameBuiltin : forall env f,
      Rename env (Builtin f) (Builtin f)
  | RenameTyInst : forall env t t' ty,
      Rename env t t' ->
      Rename env (TyInst t ty) (TyInst t' ty)
  | RenameError : forall env ty,
      Rename env (Error ty) (Error ty)
  | RenameIWrap : forall env ty1 ty2 t t',
      Rename env t t' ->
      Rename env (IWrap ty1 ty2 t) (IWrap ty1 ty2 t')
  | RenameUnwrap : forall env t t',
      Rename env t t' ->
      Rename env (Unwrap t) (Unwrap t')

(*
Non-recursive: the environment can be extended and passed down
*)
with RenameBindingsNonRec :
  environment -> (* environment passed down (accumulating param) *)
  environment ->         (* resulting environment, used for the let-body *)
  list (binding var tyvar var tyvar) -> (* bindings before translation *)
  list (binding var tyvar var tyvar) -> (* bindings after translation*)
  Type :=
  | NonRecCons : forall env env' env_up b b' bs bs',
      RenameBinding env  env_up b b' ->
      RenameBindingsNonRec (env_up ++ env) env'       bs         bs' ->
      RenameBindingsNonRec            env  env' (b :: bs) (b' :: bs')
  | NonRecNil  : forall env,
      RenameBindingsNonRec env env nil nil

(*
Recursive: the inherited environment already contains the bindings in this group,
so it does not have to be extended
*)
with RenameBindingsRec :
  environment -> (* parametrized by the environment*)
  environment ->         (* resulting environment, used for the let-body AND env parameter (see Rename_LetRec)*)
  list (binding var tyvar var tyvar) -> (* bindings before translation *)
  list (binding var tyvar var tyvar) -> (* bindings after translation*)
  Type :=
  | RecCons : forall env env_b env_bs b b' bs bs',
      RenameBinding     env  env_b            b         b'         ->
      RenameBindingsRec env           env_bs        bs         bs' ->
      RenameBindingsRec env (env_b ++ env_bs) (b :: bs) (b' :: bs')
  | RecNil  : forall env,
      RenameBindingsRec env nil nil nil

with RenameBinding :
  environment ->
  environment -> (* rename results for this binding *)
  binding var tyvar var tyvar ->
  binding var tyvar var tyvar -> Type :=

  | BindEq     : forall env s v t t' ty,
      Rename env t t' ->
      RenameBinding env [(v, Unchanged)]
        (TermBind s (VarDecl v ty) t)
        (TermBind s (VarDecl v ty) t')

  (* Todo: include the right Terms over which this binding
     is scoped, and add the ~( In free_vars ...) conditions
  *)
  (*
  | BindRename : forall env s v w t t' ty,
      v <> w ->
      ~ (In w (free_vars var_eqb t)) ->
      Rename env t t' ->
      RenameBinding env [(v, RenamedTo w)]
        (TermBind s (VarDecl v ty) t )
        (TermBind s (VarDecl w ty) t')
        *)

  | DataEq : forall env d d' env_up,
      Rename_dtdecl env env_up d d' ->
      RenameBinding env env_up
        (DatatypeBind d)
        (DatatypeBind d')

  | TypeEq : forall env t ty,
      RenameBinding env nil
        (TypeBind t ty)
        (TypeBind t ty)

with Rename_dtdecl :
  environment ->
  environment ->
  dtdecl' -> dtdecl' -> Type :=
    | Rename_Datatype : forall env var_res matchf matchf' cs_res cs cs' tv tvs ,
        Rename_var_bind env var_res matchf matchf' ->
        Rename_constrs env cs_res cs cs' ->
        Rename_dtdecl env (var_res :: cs_res)
          (Datatype tv tvs matchf  cs)
          (Datatype tv tvs matchf' cs')

(* Either a variable binder is renamed or it is equal *)
with Rename_var_bind :
  environment -> (var * rename_result) -> var -> var -> Type :=
  | VarEq  : forall env v,
      Rename_var_bind env (v, Unchanged) v v

  (* Todo: include the right Terms over which this binding
     is scoped, and add the ~( In free_vars ...) conditions
  *)
  (*
  | VarNeq : forall env v v',
      v <> v' ->
      Rename_var_bind env (v, RenamedTo v') v v'
      *)

with Rename_constrs : 
  environment ->
  environment ->
  list constr' ->
  list constr' ->
  Type :=
  | Rename_constrs_cons : forall env c cs c' cs' c_res env',
      Rename_constr env c_res c c' ->
      Rename_constrs env env' cs cs' ->
      Rename_constrs env (c_res :: env') (c :: cs) (c' :: cs')

  | Rename_constrs_nil  : forall env,
      Rename_constrs env nil nil nil

with Rename_constr :
  environment ->
  (var * rename_result) ->
  constr' ->
  constr' ->
  Type :=
  | Rename_Constructor_Eq : forall env res v v' ty arity,
      Rename_var_bind env res v v' ->
      Rename_constr
        env
        res
        (Constructor (VarDecl v  ty) arity)
        (Constructor (VarDecl v' ty) arity)
  .

End Rename.
Definition Rename_string := Rename (var := string) (tyvar := string) String.eqb nil.
