Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
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

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.


Lemma LR_reflexivity : forall ctx e T,
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
  all : eauto with DSP_compatibility_lemmas typing.
  - apply skip.
  - constructor. 
  - econstructor; eauto with DSP_compatibility_lemmas.
Qed.