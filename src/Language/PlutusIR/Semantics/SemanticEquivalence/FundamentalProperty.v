Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.Misc.Axiom.
Require Import PlutusCert.Language.PlutusIR.Semantics.Misc.BoundVars.


(*
Fundamental property (reflexivity) of LR_logically_approximate
*)

Definition P_has_type Delta Gamma e T := 
  LR_logically_approximate Delta Gamma e e T.

Definition P_constructor_well_formed Delta c Tr := Delta |-ok_c c : Tr.

Definition P_bindings_well_formed_nonrec Delta Gamma (bs : list Binding) :=
  forall Delta_t Gamma_t bsGn t t' Tn,
    Delta_t = mupdate Delta (flatten (List.map binds_Delta bs)) ->
    map_normalise (flatten (List.map binds_Gamma bs)) bsGn ->
    Gamma_t = mupdate Gamma bsGn  ->
    Delta |-* Tn : Kind_Base ->
    LR_logically_approximate Delta_t Gamma_t t t' Tn ->
    LR_logically_approximate Delta Gamma (Let NonRec bs t) (Let NonRec bs t') Tn.

Definition P_bindings_well_formed_rec Delta Gamma bs1 := Delta ,, Gamma |-oks_r bs1.

Definition P_binding_well_formed Delta Gamma b := 
  forall Delta_t Gamma_t bsGn t t' Tn bs bs',
    Delta_t = mupdate Delta (binds_Delta b) ->
    map_normalise (binds_Gamma b) bsGn ->
    Gamma_t = mupdate Gamma bsGn ->
    Delta |-* Tn : Kind_Base ->
    LR_logically_approximate Delta_t Gamma_t (Let NonRec bs t) (Let NonRec bs' t') Tn ->
    LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b :: bs') t') Tn.

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

  Local Open Scope list_scope.
  Require Import Coq.Lists.List.

Lemma LR_reflexivity : forall Delta Gamma e T,
    Delta ,, Gamma |-+ e : T ->
    LR_logically_approximate Delta Gamma e e T.
    (* P_has_type Delta Gamma e T. *)
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : autounfold; intros; subst.
  all : eauto with DSP_compatibility_lemmas typing.
  - rewrite flatten_app in H5.
    apply map_normalise__app in H5.
    destruct H5 as [l1n [l2n [Hmn__l1n [Hmn__l2n Heq]]]].
    subst.
    eapply map_normalise__deterministic in H1; eauto. 
    subst.

    eapply H0; eauto.
    eapply H3; eauto.
    + eapply Kinding.weakening; eauto.
      destruct b.
      * simpl. eapply inclusion_refl.
      * simpl. destruct t0. simpl.
        unfold inclusion.
        intros.
        destruct (s =? x)%string eqn:Heqb.
        -- eapply eqb_eq in Heqb as Heq.
           subst.
           assert (Annotation.appears_bound_in x (Let NonRec (TypeBind (TyVarDecl x k) t1 :: bs) t)) by eauto.
           eapply uniqueness' in H4.
           rewrite H4 in H1.
           inversion H1.
        -- apply eqb_neq in Heqb as Hneq.
           rewrite update_neq; eauto.
      * destruct d.
        simpl. destruct t0.
        simpl.
        unfold inclusion.
        intros.
        destruct (s0 =? x)%string eqn:Heqb.
        -- eapply eqb_eq in Heqb as Heq.
           subst.
           assert (Annotation.appears_bound_in x (Let NonRec (DatatypeBind (Datatype (TyVarDecl x k) l s l0) :: bs) t)) by eauto.
           eapply uniqueness' in H4.
           rewrite H4 in H1.
           inversion H1.
        -- apply eqb_neq in Heqb as Hneq.
           rewrite update_neq;eauto.
    + rewrite <- mupdate_app; eauto.
      rewrite <- mupdate_app; eauto.
      rewrite <- flatten_app; eauto. 
Qed.


(* Reflexivity of one-hole contexts *)

From PlutusCert Require Import
  CompatibilityLemmas.Context.C_Lam
  CompatibilityLemmas.Context.C_Apply_L
  CompatibilityLemmas.Context.C_Apply_R
  CompatibilityLemmas.Context.C_Hole.

Create HintDb hintdb_compat_context.
#[global]
Hint Resolve
  compatibility_C_Hole
  compatibility_C_LamAbs
  compatibility_C_Apply_L
  compatibility_C_Apply_R

  LR_reflexivity
  : hintdb_compat_context.

Hint Unfold P_has_type : hintdb_compat_context.

Lemma LR_reflexivity_context : forall C Δ₁ Γ₁ Δ Γ T T₁,
  Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
  LR_logically_approximate_context Δ₁ Γ₁ C C Δ Γ T T₁.
Proof with eauto with hintdb_compat_context.
  induction C.

  all: intros Δ₁ Γ₁ Δ Γ T T₁ H_C_ty.
  all: inversion H_C_ty; subst...
Qed.
