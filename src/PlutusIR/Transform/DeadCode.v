From Coq Require Import
  Strings.String
  Lists.List
  Utf8_core
.

From Equations Require Import Equations.

From PlutusCert Require Import
  Util
  Util.List
  PlutusIR
  PlutusIR.Analysis.FreeVars
  PlutusIR.Analysis.Equality
  PlutusIR.Analysis.Purity
  PlutusIR.Analysis.WellScoped
  PlutusIR.Analysis.UniqueBinders
  PlutusIR.Transform.Compat
  PlutusIR.Semantics.Dynamic.Values
.

Import NamedTerm.
Import UniqueBinders.Term.
Import ListNotations.

Set Implicit Arguments.
Set Equations Transparent.


Notation fv := (free_vars String.eqb).
Notation fv_binding := (free_vars_binding String.eqb).
Notation fv_bindings := (free_vars_bindings String.eqb fv_binding).

Definition name_Binding (b : Binding) :=
  match b with
    | TermBind s (VarDecl x _) t => x
    | TypeBind (TyVarDecl x _) ty => x
    | DatatypeBind (Datatype (TyVarDecl x _) _ _ _) => x
  end.

(* Whether *)
Definition name_removed b bs : Prop :=
  ¬ (In (name_Binding b) (map name_Binding bs)).

Inductive elim : Term -> Term -> Prop :=
  | elim_compat : forall t t',
      Compat elim t t' ->
      elim t t'

  | elim_delete_let : forall rec bs t t',
      elim t t' ->
      Forall (pure_binding []) bs ->
      elim (Let rec bs t) t'

  | elim_delete_bindings : forall rec bs bs' t t',
      elim t t' ->
      elim_bindings bs bs' ->
      elim (Let rec bs t) (Let rec bs' t')

  | elim_delete_ty_beta : forall t t' α k τ,
      elim t t' ->
      elim (TyInst (TyAbs α k t) τ) t'


with elim_bindings : list Binding -> list Binding -> Prop :=
  | elim_bindings_pure : forall bs bs',

      (* any removed binding is a pure binding *)
      (∀ b, In b bs ->
        name_removed b bs' -> pure_binding [] b
      ) ->

      (* Any resulting binding has a (related) binding in the original group *)
      (∀ b', In b' bs' ->
         ∃ b, In b bs /\
           name_Binding b = name_Binding b' /\
           elim_binding b b'
      ) ->
      elim_bindings bs bs'

with elim_binding : Binding -> Binding -> Prop :=

  | elim_term_bind_compat : forall s vd t t',
      elim t t' ->
      elim_binding (TermBind s vd t) (TermBind s vd t')

  | elim_binding_refl : forall b,
      elim_binding b b
  .

Definition dead_code t t' := elim t t' /\ unique t /\ closed t'.

Lemma elim_sym : forall t, elim t t.
Admitted.