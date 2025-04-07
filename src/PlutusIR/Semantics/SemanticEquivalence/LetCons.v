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


From PlutusCert Require Import DeadCode.DSP.Lemmas.
From PlutusCert Require Import DeadCode.DSP.BoundVars.
From PlutusCert Require Import Substitution.Free.
From PlutusCert Require Import SubstitutionPreservesTyping.

Import Utf8_core.

Import ListNotations.

Notation close γ ρ t := (msubst γ (msubstA ρ t)).

(* New LR *)
Notation "Δ ',,' Γ '|-' e1 ≤ e2 ':' T" := (approx Δ Γ e1 e2 T)
  ( at level 101
  , e1 at level 0
  , e2 at level 0
  , T at level 0
  , no associativity).


Definition msubstA_LetNonRec (ρ : list (string * ty)) bs e :
  ρ ⊙ Let NonRec bs e =
  Let NonRec (ρ ⊙ bs) (ρ - bs ⊙ e).
Admitted.

Definition msubst_LetNonRec (γ : list (string * term)) bs e :
  γ ⊙ Let NonRec bs e =
  Let NonRec (γ ⊙ bs) (γ - bs ⊙ e).
Admitted.

Definition msubstA_BindingsNonRec_cons
     : ∀ (ss : list (string * ty)) (b : binding) (bs : list binding),
         ss ⊙ (b :: bs) =
         ss ⊙ b :: ss - b ⊙ bs.
Admitted.


Axiom msubst_bnr_cons
     : ∀ (ss : list (string * term)) (b : binding) (bs : list binding),
         ss ⊙ (b :: bs) =
         ss ⊙ b :: ss - b ⊙ bs
.

Lemma elim_TermBind_NonRec__approximate Δ Γ t Tn b bs:
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : Tn ->
  Δ ,, Γ |- (Let NonRec (b :: bs) t) ≤ (Let NonRec [b] (Let NonRec bs t)) : Tn.
Proof.
  intros H_typing.
  unfold approx.
  split; try assumption.
  split.
  - admit. (* TODO: typing rules *)
  - (* C *)
    intros k ρ γ γ' H_D H_G.
    autorewrite with R.
    intros j H_j_k r H_eval_r.

    rewrite msubstA_LetNonRec, msubst_LetNonRec, msubstA_BindingsNonRec_cons,  msubst_bnr_cons
        in H_eval_r.
    remember (msyn1 ρ) as ρ₁.
    remember (msyn2 ρ) as ρ₂.
      inversion H_eval_r. subst.
      inversion H3. subst.
      * (* TermBind *)
      rewrite <- msubst_LetNonRec in H8.
      rewrite msubstA_LetNonRec, msubst_LetNonRec, msubstA_BindingsNonRec_cons,  msubst_bnr_cons
        in H_eval_r.
      rewrite msubstA_LetNonRec, msubst_LetNonRec, msubstA_BindingsNonRec_cons,  msubst_bnr_cons.
      constructor.
      econstructor.
    eexists. eexists.
    split.
    + rewrite msubstA_LetNonRec, msubst_LetNonRec, msubstA_BindingsNonRec_cons,  msubst_bnr_cons
        in H_eval_r.
      inversion H_eval_r. subst.
      inversion H3. subst.
      * (* TermBind *)
      rewrite msubstA_LetNonRec, msubst_LetNonRec, msubstA_BindingsNonRec_cons,  msubst_bnr_cons.
      constructor.
      econstructor.

    simpl in H_eval_r.


