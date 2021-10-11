Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Apply.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Builtin.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.DatatypeBind.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Error.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.ExtBuiltin.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.IWrap.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LamAbs.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LetNonRec.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.LetRec.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Unwrap.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TermBind.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyAbs.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TyInst.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.TypeBind.
Require Export PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Var.

Create HintDb DSP_compatibility_lemmas.
#[export] Hint Resolve 
  compatibility_Apply
  compatibility_Builtin
  compatibility_Constant
  compatibility_DatatypeBind
  compatibility_Error
  compatibility_ExtBuiltin
  compatibility_IWrap
  compatibility_LamAbs
  compatibility_LetNonRec_nil
  compatibility_LetNonRec_cons
  compatibility_LetRec
  compatibility_TermBind
  compatibility_TyAbs
  compatibility_TyInst
  compatibility_TypeBind
  compatibility_Unwrap
  compatibility_Var : DSP_compatibility_lemmas.

Require Import Coq.Lists.List.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.

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

Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Lemma helper : forall Delta Gamma b bs e e' T,
    LR_logically_approximate 
      (mupdate Delta (flatten (List.map binds_Delta (b :: bs)))) 
      (mupdate Gamma (flatten (List.map binds_Gamma (b :: bs))))
      e e' T ->
    LR_logically_approximate
      (mupdate (mupdate Delta (binds_Delta b)) (flatten (List.map binds_Delta bs)))
      (mupdate (mupdate Gamma (binds_Gamma b)) (flatten (List.map binds_Gamma bs)))
      e e' T.
Proof.
  intros.
  rewrite <- mupdate_app.
  rewrite <- mupdate_app.
  rewrite <- flatten_app.
  rewrite <- flatten_app.
  assumption.
Qed.

#[export] Hint Resolve helper : DSP_compatibility_lemmas.