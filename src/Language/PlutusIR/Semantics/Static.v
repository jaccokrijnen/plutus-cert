(** The static semantics *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Rules.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Normalisation.

(** Important theorems *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.FreeInContext.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.UniqueTypes.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.Weakening.

(** Hint database *)
Create HintDb typing.
#[export] Hint Constructors has_kind : typing.
#[export] Hint Constructors has_type : typing.
#[export] Hint Constructors constructor_well_formed : typing.
#[export] Hint Constructors bindings_well_formed_nonrec : typing.
#[export] Hint Constructors bindings_well_formed_rec : typing.
#[export] Hint Constructors binding_well_formed : typing.