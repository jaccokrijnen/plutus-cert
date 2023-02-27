(** The static semantics *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Normalisation.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Typing.

(** Important theorems *)
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.FreeInContext.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Theorems.In_Auxiliary.
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
#[export] Hint Constructors appears_free_in_ty : typing.
#[export] Hint Constructors appears_free_in_tm : typing.
#[export] Hint Constructors appears_free_in_ann : typing.
#[export] Hint Resolve 
  normalise_to_normal
  normalisation__deterministic
  normalisation__stable 
  has_type__normal
  : typing.
