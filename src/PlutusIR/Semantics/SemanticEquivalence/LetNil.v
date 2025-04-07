From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import BaseKindedness.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import SemanticEquivalence.CompatibilityLemmas.
From PlutusCert Require Import SemanticEquivalence.Auto.
From PlutusCert Require Import SemanticEquivalence.FundamentalProperty.
From PlutusCert Require Import Substitution.
From PlutusCert Require Import Util.Tactics.

From PlutusCert Require Import Multisubstitution.Congruence.
From PlutusCert Require Import Util.List.

Import PlutusNotations.

From PlutusCert Require Import DeadCode.DSP.Lemmas.
From PlutusCert Require Import DeadCode.DSP.BoundVars.
From PlutusCert Require Import Substitution.Free.
From PlutusCert Require Import SubstitutionPreservesTyping.

Import Utf8_core.

Import ListNotations.

Notation close γ ρ t := (msubst γ (msubstA ρ t)).


Lemma has_type__Let_Nil_inv Δ Γ t T :
  Δ ,, Γ |-+ (Let NonRec [] t) : T ->
  Δ ,, Γ |-+ t : T.
Proof.
    inversion 1. subst.
    inversion H3. subst.
    assumption.
Qed.

Lemma elim_TermBind_NonRec__approximate Δ Γ t Tn :
  Δ ,, Γ |-+ (Let NonRec [] t) : Tn ->
  Δ ,, Γ |- (Let NonRec [] t) ≤ t : Tn.
Proof.
  intros H_ty.
  unfold LR_logically_approximate.
  split; try assumption.
  split.
  - (* typing *)
    inversion H_ty. subst.
    inversion H2. subst.
    assumption.
  -
    intros k ρ γ γ' H_D H_G.
    autorewrite with RC.
    intros j H_j_k r H_eval_r.

      rewrite msubstA_LetNonRec_nil, msubst_LetNonRec_nil  in H_eval_r.
      inversion H_eval_r. subst.
      inversion H3. subst.
      assert (H_refl_t : Δ ,, Γ |- t ≤ t : Tn). {
        apply LR_reflexivity.
        inversion H_ty. subst. inversion H4. subst.
        simpl in H9.
        assumption.
      }
      destruct H_refl_t as [_ [ _ H_C]].
      specialize (H_C _ ρ γ γ' H_D H_G).
      autorewrite with RC in H_C.
      specialize (H_C j1 ltac:(lia) _ H1).
      destruct_hypos.
    eexists. eexists.
    repeat split.
    + exact H.
    + (* TODO *)
Admitted.



(* New LR *)
Notation "Δ ',,' Γ '|-' e1 ≤ e2 ':' T" := (approx Δ Γ e1 e2 T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).


Axiom approx_refl : ∀ (Δ : list (string * kind)) (Γ : list (string * ty)) (t : term) (T : ty),
  Δ,, Γ |-+ t : T ->
  Δ ,, Γ |- t ≤ t : T.

Lemma approx_Let_NonRec_nil Δ Γ t T :
  Δ ,, Γ |-+ (Let NonRec [] t) : T ->
  Δ ,, Γ |- (Let NonRec [] t) ≤ t : T.
Proof.
  intros H_ty.
  unfold approx.
  assert (H_ty' : Δ ,, Γ |-+ t : T) by auto using has_type__Let_Nil_inv.
  repeat split.
  - assumption.
  - assumption.
  - intros k ρ γ γ' H_D H_G.
    autorewrite with R.
    intros j H_j_k r.
    intros H_eval.
    rewrite msubstA_LetNonRec_nil, msubst_LetNonRec_nil  in H_eval.
    inversion_clear H_eval.
    inversion_clear H.
    assert (H_t_refl : Δ ,, Γ |- t ≤ t : T). { apply approx_refl. assumption. }
    destruct H_t_refl as [ _ [ _ H_C]].
    (* apply G_monotone with (Δ := Δ) (i := j) in H_G; try solve [assumption | lia]. *)
    specialize (H_C k _ _ _ H_D H_G).
    autorewrite with R in H_C.
    specialize (H_C j1 ltac:(lia) _ H1).
    destruct_hypos.
    exists x, x0.
    split.
    + assumption.
    + destruct H2.
      * apply V_monotone with (Δ := Δ) (i := k - j) in H2;try solve [assumption | lia].
        left. assumption.
      * right. assumption.
Qed.
