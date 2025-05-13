Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Apply.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Builtin.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.DatatypeBind.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Error.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.IWrap.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LamAbs.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LetNonRec.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LetRec.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TermBind.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyAbs.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyAbs2.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyInst.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TypeBind.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Unwrap.
Require Export PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Var.

Create HintDb DSP_compatibility_lemmas.
#[export] Hint Resolve
  compatibility_Apply
  compatibility_Builtin
  compatibility_Constant
  compatibility_DatatypeBind
  compatibility_Error
  compatibility_IWrap
  compatibility_LamAbs
  compatibility_LetNonRec_Nil
  compatibility_LetRec
  compatibility_TermBind
  compatibility_TyAbs
  compatibility_TyAbs2
  compatibility_TyInst
  compatibility_TypeBind
  compatibility_Unwrap
  compatibility_Var : DSP_compatibility_lemmas.

Require Import Coq.Lists.List.
Require Import PlutusCert.PlutusIR.Semantics.Static.

Lemma flatten_app : forall {A B : Type} (f : A -> list B) (l : list A) x,
    flatten (List.map f (x :: l)) = flatten (List.map f l) ++ f x.
Proof.
  intros.
  unfold flatten.
  simpl.
  rewrite concat_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.