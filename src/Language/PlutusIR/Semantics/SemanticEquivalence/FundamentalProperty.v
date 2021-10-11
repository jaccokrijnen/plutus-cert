Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.


Definition P_has_type Delta Gamma e T := 
  LR_logically_approximate Delta Gamma e e T.

Definition P_constructor_well_formed Delta c := Delta |-ok_c c.

Definition P_bindings_well_formed_nonrec Delta Gamma (bs : list Binding) := 
  forall Delta_t Gamma_t t t' T,
    Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
    Gamma_t = mupdate Gamma (flatten (List.map binds_Gamma bs)) ->
    LR_logically_approximate Delta_t Gamma_t t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs t') T.

Definition P_bindings_well_formed_rec Delta Gamma bs1 := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b := 
    LR_logically_approximate_binding Delta Gamma b b.

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.


Lemma LR_reflexivity : forall Delta Gamma e T,
    Delta ,, Gamma |-+ e : T ->
    P_has_type Delta Gamma e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : autounfold; intros; subst.
  all : eauto with DSP_compatibility_lemmas typing.
Qed.