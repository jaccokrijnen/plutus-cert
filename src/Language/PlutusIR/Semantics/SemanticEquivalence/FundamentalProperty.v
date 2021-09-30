Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Util.

(** ** The [R] Lemma *)


Definition P_has_type ctx e T := 
  LR_logically_approximate (fst ctx) (snd ctx) e e T.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs := 
  LR_logically_approximate_bindings_nonrec (fst ctx) (snd ctx) bs bs.

Definition P_bindings_well_formed_rec ctx bs1 := ctx |-oks_r bs1.

Definition P_binding_well_formed ctx b := 
  LR_logically_approximate_binding (fst ctx) (snd ctx) b b.

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



Lemma msubst_R : forall ctx e T,
    ctx |-+ e : T ->
    P_has_type ctx e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : unfold P_has_type; intros; subst.
  all : eauto with DSP_compatibility_lemmas.
  - apply skip.
  - unfold P_constructor_well_formed. eauto with typing.
  - unfold P_bindings_well_formed_nonrec. constructor. 
  - unfold P_bindings_well_formed_nonrec. econstructor; eauto with DSP_compatibility_lemmas.
  - unfold P_bindings_well_formed_rec. eauto with typing.
  - unfold P_bindings_well_formed_rec. eauto with typing.
  - apply skip. (* TODO *)
  - apply skip. (* TODO *)
  - apply skip. (* TODO *)
Qed.