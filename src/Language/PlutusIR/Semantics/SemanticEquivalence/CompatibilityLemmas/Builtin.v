Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.



Lemma msubst_Builtin : forall ss f,
    msubst_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_Builtin : forall ss f,
    msubstA_term ss (Builtin f) = Builtin f.
Proof. 
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyFun : forall ss T1 T2,
    msubstT ss (Ty_Fun T1 T2) = Ty_Fun (msubstT ss T1) (msubstT ss T2).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    apply IHss.
Qed.

Lemma compatibility_Builtin: forall Δ Γ f T Tn,
    T = lookupBuiltinTy f ->
    normalise T Tn ->
    LR_logically_approximate Δ Γ (Builtin f) (Builtin f) Tn.
Proof with eauto_LR.
  intros Δ Γ f Hlu Hnorm__Tn.
  unfold LR_logically_approximate.

  split...
  split...

  intros k ρ γ γ' H_RD H_RG.
  subst.

  rewrite msubstA_Builtin. rewrite msubstA_Builtin.
  rewrite msubst_Builtin. rewrite msubst_Builtin.

  autorewrite with RC.
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f; subst.
(* ADMIT: We do not handle built-in functions yet. *)
Admitted.
