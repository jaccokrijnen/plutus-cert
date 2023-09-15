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

Inductive elim : Term -> Term -> Prop :=
  | elim_compat : forall t t',
      Compat elim t t' ->
      elim t t'

  | elim_let : forall rec bs t t',
      elim t t' ->
      Forall (pure_binding []) bs ->
      elim (Let rec bs t) t'

  | elim_let_bindings : forall rec bs bs' t t',
      elim t t' ->
      elim_bindings bs bs' ->
      elim (Let rec bs t) (Let rec bs' t')


with elim_bindings : list Binding -> list Binding -> Prop :=

  | elim_bindings_keep : forall b b' bs bs',
      elim_binding b b' ->
      elim_bindings bs bs' ->
      elim_bindings (b :: bs) (b' :: bs')

  | elim_bindings_drop : forall b bs bs',
      pure_binding [] b ->
      elim_bindings bs bs' ->
      elim_bindings (b :: bs) bs'

  | elim_bindings_nil :
      elim_bindings [] []

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
