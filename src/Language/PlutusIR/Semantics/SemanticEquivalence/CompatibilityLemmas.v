(*Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Apply.*)
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.IWrap.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LamAbs.
(*Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Unwrap.*)
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyAbs.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Var.


Create HintDb DSP_compatibility_lemmas.
#[export] Hint Resolve 
  compatibility_Constant
  compatibility_IWrap
  compatibility_LamAbs
  compatibility_TyAbs
  compatibility_Var : DSP_compatibility_lemmas.