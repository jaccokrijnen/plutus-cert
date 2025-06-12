(** The static semantics *)
Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.BigStep.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.Typing.
Require Export PlutusCert.PlutusIR.Semantics.Static.Typing.drop_context.

(** Important theorems *)
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.FreeInContext.
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.In_Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.UniqueTypes.
Require Export PlutusCert.PlutusIR.Semantics.Static.Theorems.Weakening.

(** Hint database *)
Create HintDb typing.
#[export] Hint Constructors has_kind : typing.
#[export] Hint Constructors has_type : typing.
#[export] Hint Constructors constructor_well_formed : typing.
#[export] Hint Constructors bindings_well_formed_nonrec : typing.
#[export] Hint Constructors bindings_well_formed_rec : typing.
#[export] Hint Constructors binding_well_formed : typing.
#[export] Hint Constructors Ty.appears_free_in : typing.
#[export] Hint Constructors Term.appears_free_in : typing.
#[export] Hint Constructors Annotation.appears_free_in : typing.
#[export] Hint Resolve
  normalise_to_normal
  normalisation__deterministic
  normalisation__stable
  has_type__normal
  : typing.
