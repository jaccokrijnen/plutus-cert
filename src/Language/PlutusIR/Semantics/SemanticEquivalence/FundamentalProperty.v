Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.


(** ** The [R] Lemma *)


Definition P_has_type Gamma e T := 
  LR_logically_approximate (fst Gamma) (snd Gamma) e e T.

Definition P_constructor_well_formed Gamma c := Gamma |-ok_c c.

Definition P_bindings_well_formed_nonrec Gamma bs1 := Gamma |-oks_nr bs1.

Definition P_bindings_well_formed_rec Gamma bs1 := Gamma |-oks_r bs1.

Definition P_binding_well_formed Gamma b1 := Gamma |-ok b1.

Axiom skip : forall P, P.

 (*forall c e1 e2 t1 t2 T,
    (mupdate emptyContext c) |-+ t1 : T ->
    (mupdate emptyContext c) |-+ t2 : T ->
    instantiation c e1 e2 ->
    CNR_Term t1 t2 ->
    forall t1' t2',
      msubst e1 t1 t1' ->
      msubst e2 t2 t2' ->
      R T t1' t2'.*)

Lemma msubst_R : forall Gamma e T,
    Gamma |-+ e : T ->
    P_has_type Gamma e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : unfold P_has_type; intros; subst.
  all : eauto with DSP_compatibility_lemmas.
  - intros. unfold P_has_type. intros. subst.
    apply skip.
  - intros. unfold P_has_type. intros. subst.
    apply skip.

  - (* T_TyInst *)
    intros.
    unfold P_has_type.
    unfold LR_logically_approximate.
    
    apply skip.
  - unfold P_constructor_well_formed. eauto with typing.
  - unfold P_bindings_well_formed_nonrec. eauto with typing.
  - unfold P_bindings_well_formed_nonrec. eauto with typing.
  - unfold P_bindings_well_formed_rec. eauto with typing.
  - unfold P_bindings_well_formed_rec. eauto with typing.
  - unfold P_binding_well_formed. eauto with typing.
  - unfold P_binding_well_formed. eauto with typing.
  - unfold P_binding_well_formed. eauto with typing. 
Qed.