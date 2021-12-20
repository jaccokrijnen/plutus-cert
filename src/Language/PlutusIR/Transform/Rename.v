From Coq Require Import
  String
  List
  Unicode.Utf8_core
  .
From PlutusCert Require Import
  Util
  Language.PlutusIR
  Transform.Congruence
  Analysis.BoundVars
  Analysis.FreeVars
  .


Section Rename.
Context
  {var tyvar : Set}
  (var_eqb : var -> var -> bool).

Definition term' := term var tyvar var tyvar.
Definition binding' := binding var tyvar var tyvar.
Notation dtdecl' := (dtdecl tyvar var tyvar).
Notation constr' := (constr tyvar var tyvar).


Import ListNotations.


Definition environment := list (var * var).

Definition renamed_from (v : var) : environment -> list var :=
  map snd ∘ filter (var_eqb v ∘ fst).

Definition renamed_to (v : var) : environment -> list var :=
  map fst ∘ filter (var_eqb v ∘ snd).


Definition safe_head {a : Type} (xs : list a) : option a :=
  match xs with
    | cons x _ => Datatypes.Some x
    | nil => None
  end
.

Definition lookup (v : var) : environment -> option var :=
  safe_head ∘ renamed_from v
.


(* Get the term from a Termbind, or None*)
Definition binding_term (b : binding') : option term' :=
  match b with
    | TermBind _ _ t => Datatypes.Some t
    | _ => None
    end
  .




Inductive var_scope :=
  | LamScope       : term' -> var_scope

  (* A bound var in let nonrec scopes over the rest of the bindings
     and the let-body
  *)
  | LetNonRecScope : term' -> list binding' -> var_scope

  (* A bound var in let rec scopes over the let-body and  all rhs' in that
     group, there should be no shadowing of other binders in that group
  *)
  | LetRecScope    : list term' -> var_scope .


(*
Given the renaming (v, w), and the terms ts_v that v scopes over,
there should be no (x, w) ∈ Δ such that x occurs free in ts_v, otherwise
this renaming will capture it
*)
Definition no_capture
  (Δ : environment)
  (scope : var_scope)
  (renaming : var * var) : Prop :=
  match renaming with
    | (v, w) => ∀ x, In x (renamed_to w Δ) ->
      match scope with
        | LamScope t          => ~In x (free_vars var_eqb t)
        | LetNonRecScope t bs => ~In x (free_vars var_eqb t) *
                                ~In x (free_vars_bindings var_eqb NonRec bs)
        | LetRecScope ts      => Forall (fun t => ~ In x (free_vars var_eqb t)) ts
      end
  end
  .

Definition binding_rhs (b : binding') : option term' :=
  match b with
    | TermBind _ _ t => Datatypes.Some t
    | TypeBind _ _   => Datatypes.None
    | DatatypeBind _ => Datatypes.None
 end.

Definition mkLetScope (rec : Recursivity) (t_body : term') (bs : list binding')
  : var_scope :=
  match rec with
    | Rec    => LetRecScope (t_body :: map_option binding_rhs bs)
    | NonRec => LetNonRecScope t_body bs
  end.


(* Alpha renaming of term variables *)
Polymorphic Inductive Rename : environment -> term' -> term' -> Type :=
  | RenameLamAbs : forall Δ v w ty t t',
      no_capture Δ (LamScope t) (v, w) ->
      Rename ((v, w) :: Δ) t t' ->
      Rename Δ (LamAbs v ty t) (LamAbs w ty t')

  | RenameVar : forall Δ v w,
      lookup v Δ = Datatypes.Some w ->
      Rename Δ (Var v) (Var w)

  | RenameLetNonRec : forall Δ bs bs' Δ' t t',
      RenameBindingsNonRec Δ t Δ' bs bs' ->
      Rename Δ' t t' ->
      Rename Δ (Let NonRec bs t) (Let NonRec bs' t')

  | RenameLetRec    : forall Δ bs bs' Δ' t t',
      NoDup (bound_vars_bindings bs') ->
      RenameBindingsRec Δ t bs Δ' bs bs' ->
      Rename Δ' t t' ->
      Rename Δ (Let Rec bs t) (Let Rec bs' t')

  (* The rest are congruence rules *)

  | RenameTyAbs : forall Δ ty k t t',
      Rename Δ t t' ->
      Rename Δ (TyAbs ty k t) (TyAbs ty k t')

  | RenameApply : forall Δ t1 t2 t1' t2',
      Rename Δ t1 t1' ->
      Rename Δ t2 t2' ->
      Rename Δ (Apply t1 t2) (Apply t1' t2')

  | RenameConstant : forall Δ c,
      Rename Δ (Constant c) (Constant c)

  | RenameBuiltin : forall Δ f,
      Rename Δ (Builtin f) (Builtin f)

  | RenameTyInst : forall Δ t t' ty,
      Rename Δ t t' ->
      Rename Δ (TyInst t ty) (TyInst t' ty)

  | RenameError : forall Δ ty,
      Rename Δ (Error ty) (Error ty)

  | RenameIWrap : forall Δ ty1 ty2 t t',
      Rename Δ t t' ->
      Rename Δ (IWrap ty1 ty2 t) (IWrap ty1 ty2 t')

  | RenameUnwrap : forall Δ t t',
      Rename Δ t t' ->
      Rename Δ (Unwrap t) (Unwrap t')



(*
Non-recursive: the environment can be extended and passed down
*)
with RenameBindingsNonRec :
  environment   -> (* environment passed down (accumulating param) *)
  term'         -> (* the let body of this binding group (before transformation) *)
  environment   -> (* renamings resulting from the following bindings (bottom up), used for the let-body *)
  list binding' -> (* bindings before translation *)
  list binding' -> (* bindings after translation*)
  Type :=

  | NonRecCons : forall Δ t_body Δ' Δ_up b b' bs bs',
      RenameBinding Δ NonRec bs t_body Δ_up b b' ->
      RenameBindingsNonRec (Δ_up ++ Δ) t_body Δ'       bs         bs' ->
      RenameBindingsNonRec          Δ  t_body Δ' (b :: bs) (b' :: bs')

  | NonRecNil  : forall Δ t_body,
      RenameBindingsNonRec Δ t_body Δ nil nil


with RenameBindingsRec :
  environment   -> (* parametrized by the environment*)
  term'         -> (* the let body of this binding group *)
  list binding' -> (* _all_ other bindings in this group (before transformation) *)
  environment   -> (* resulting environment, used for the let-body AND env parameter (see Rename_LetRec)*)
  list binding' -> (* rest of bindings before translation *)
  list binding' -> (* rest of bindings after translation*)
  Type :=

  | RecCons : forall Δ t_body all_bs Δ_b Δ_bs b b' bs bs',
      RenameBinding     Δ Rec all_bs t_body  Δ_b           b         b'        ->
      RenameBindingsRec Δ t_body all_bs         Δ_bs        bs         bs' ->
      RenameBindingsRec Δ t_body all_bs (Δ_b ++ Δ_bs) (b :: bs) (b' :: bs')

  | RecNil  : forall Δ t_body all_bs,
      RenameBindingsRec Δ t_body all_bs nil nil nil

with RenameBinding :
  environment   ->
  Recursivity   -> (* recursivity of this let group *)
  list binding' -> (* bindings in group that this binding scopes over (before transformation) *)
  term'         -> (* let-body it scopes over (before transformation) *)
  environment   -> (* rename results for this binding *)
  binding'      ->
  binding'      ->
  Type :=

  | RenameTermBind : ∀ Δ rec bs t_body s v w t t' ty,
      no_capture Δ (mkLetScope rec t_body bs) (v, w) ->
      Rename Δ t t' ->
      RenameBinding Δ rec bs t_body [(v, w)]
        (TermBind s (VarDecl v ty) t)
        (TermBind s (VarDecl w ty) t')

  | RenameDatatypeBind : ∀ Δ rec bs t_body Δ_data Δ_cs tv tvs cs cs' m m',
      Rename_constrs Δ_cs cs cs' ->       (* The renames of the constructors *)
      Δ_data = ((m, m') :: Δ_cs) ->       (* The renames in the datatype are the rename of the matching and the renames of the constructors*)
      NoDup (map snd Δ_data) ->           (* preserves well-scopedness (see note in problems/transform/rename-preconditions )*)
      ForallT (no_capture Δ (mkLetScope rec t_body bs)) Δ_data ->
      RenameBinding Δ rec bs t_body Δ_data
        (DatatypeBind (Datatype tv tvs m  cs))
        (DatatypeBind (Datatype tv tvs m' cs'))

  | RenameTypeBind  : ∀ Δ rec bs t_body  tv ty,
      RenameBinding Δ rec bs t_body nil
        (TypeBind tv ty)
        (TypeBind tv ty)

with Rename_constrs :
  environment -> (* The renamings in each constructor (bottom-up) *)
  list constr' ->
  list constr' ->
  Type :=
  | Rename_constrs_cons : forall rename Δ_cs c cs c' cs',
      Rename_constr rename c c' ->
      Rename_constrs Δ_cs cs cs' ->
      Rename_constrs (rename :: Δ_cs) (c :: cs) (c' :: cs')

  | Rename_constrs_nil :
      Rename_constrs nil nil nil

with Rename_constr :
  (var * var) ->
  constr' ->
  constr' ->
  Type :=
  | RenameConstructor : forall v w ty arity,
      Rename_constr
        (v, w)
        (Constructor (VarDecl v ty) arity)
        (Constructor (VarDecl w ty) arity)
  .

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
End Rename.
Definition Rename_string := Rename (var := string) (tyvar := string) String.eqb nil.

