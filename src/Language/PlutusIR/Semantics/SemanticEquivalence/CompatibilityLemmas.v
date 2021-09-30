Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Apply.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Builtin.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Error.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.IWrap.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LamAbs.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LetNonRec.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Unwrap.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyAbs.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyInst.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Var.


Create HintDb DSP_compatibility_lemmas.
#[export] Hint Resolve 
  compatibility_Apply
  compatibility_Builtin
  compatibility_Constant
  compatibility_Error
  compatibility_IWrap
  compatibility_LamAbs
  compatibility_LetNonRec
  compatibility_TyAbs
  compatibility_TyInst
  compatibility_Unwrap
  compatibility_Var : DSP_compatibility_lemmas.


Lemma distr_projection_application : forall {A B C D: Type} (f : A * B -> C * D) (p : A * B),
    (fst (f p), snd (f p)) = f (fst p, snd p).
Proof. destruct p. simpl. destruct f. simpl. reflexivity. Qed.

#[export] Hint Resolve distr_projection_application : DSP_compatibility_lemmas.