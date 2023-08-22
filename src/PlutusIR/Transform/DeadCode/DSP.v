Require Import PlutusCert.PlutusIR.Transform.DeadCode2.
Require Import PlutusCert.PlutusIR.Transform.DeadCode.SSP.
Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.

Import PlutusNotations.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.



(** ** Predicates *)

Definition P_has_type Δ Γ t T : Prop :=
  forall t',
    dc t t' ->
    Δ ,, Γ |- t ≤ t' : T.

Definition P_constructor_well_formed Δ c Tr : Prop := Δ |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Δ Γ bs : Prop :=
  (
    forall bs',
      Compat.Compat_Bindings dc bs bs' ->
      forall Δ_t Γ_t bsGn t t' Tn,
        Δ_t = flatten (List.map binds_Delta bs) ++ Δ  ->
        map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
        Γ_t = bsGn ++ Γ ->
        Δ |-* Tn : Kind_Base ->
        Δ_t ,, Γ_t |- t ≤ t' : Tn ->
        Δ   ,, Γ   |- (Let NonRec bs t) ≤ (Let NonRec bs' t') : Tn
  ).

Definition P_bindings_well_formed_rec Δ Γ bs1 : Prop := Δ ,, Γ |-oks_r bs1.

Definition P_binding_well_formed Δ Γ b : Prop :=
  (
    forall b',
      Compat.Compat_Binding dc b b' ->
      forall Δ_t Γ_t bsGn t t' Tn bs bs',
        Δ_t = binds_Delta b ++ Δ ->
        map_normalise (binds_Gamma b) bsGn ->
        Γ_t = bsGn ++ Γ ->
        Δ |-* Tn : Kind_Base ->
        Δ_t ,, Γ_t |- (Let NonRec bs t) ≤ (Let NonRec bs' t') : Tn ->
        Δ   ,, Γ   |- (Let NonRec (b :: bs) t) ≤ (Let NonRec (b' :: bs') t') : Tn
  ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

(** ** The main theorem *)

Theorem CNR_Term__DSP : forall Δ Γ e T,
    Δ ,, Γ |-+ e : T ->
    P_has_type Δ Γ e T.
Proof with (eauto_LR || eauto with DSP_compatibility_lemmas).
  apply has_type__ind with
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  all : intros; autounfold; intros; subst.
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

  (* T_Let *)
  - inversion X; subst.

    (* dc_compat *)
    + inversion X0.
      eapply H3...

    (* dc_delete_binding *)
    + admit.
      (* TODO: use TermBind/TypeBind/DatatypeBind lemmas *)

    (* dc_keep_binding *)
    + admit.

    (* dc_delete_let_nil *)
    + admit.

    (* dc_compat_let_nil_nil *)
    + admit.

  (* W_NilB_NonRec *)
  - inversion X. subst.
    simpl in H3...

  (* W_ConsB_NonRec *)
  - inversion X. subst.

    admit.

Admitted.
