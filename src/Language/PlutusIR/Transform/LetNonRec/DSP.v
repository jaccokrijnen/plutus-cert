Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Util.

Definition P_has_type ctx e T := 
  forall e',
    CNR_Term e e' ->
    LR_logically_approximate (fst ctx) (snd ctx) e e' T.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs := 
  forall bs',
    Congruence.Cong_Bindings CNR_Term bs bs' ->
    LR_logically_approximate_bindings_nonrec (fst ctx) (snd ctx) bs bs'.

Definition P_bindings_well_formed_rec ctx bs1 := ctx |-oks_r bs1.

Definition P_binding_well_formed ctx b := 
  forall b',
    Congruence.Cong_Binding CNR_Term b b' ->
    LR_logically_approximate_binding (fst ctx) (snd ctx) b b'.

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

Lemma CNR_Term__DSP : forall ctx e T,
    ctx |-+ e : T ->
    P_has_type ctx e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : autounfold; intros; subst.
  all : try solve [
    inversion X; subst;
    inversion X0; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    inversion X0; subst;
    inversion X1; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    eauto with typing
  ].
  - inversion X.
    + subst.
      apply skip.
    + subst.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas.
  - apply skip.
  - inversion X. subst. 
    constructor. 
  - inversion X. subst. 
    econstructor.
    all: eauto with DSP_compatibility_lemmas. 
    inversion X0. 
    subst. 
    all: eauto.
Qed.