Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.



Lemma msubst_Constant : forall ss sv,
    msubst_term ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a.
    eauto.
Qed.

Lemma msubstA_Constant : forall ss sv ,
    msubstA_term ss (Constant sv) = Constant sv.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstT_TyBuiltin : forall ss u,
    msubstT ss (Ty_Builtin (Some (TypeIn u))) = Ty_Builtin (Some (TypeIn u)).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma compatibility_Constant : forall Δ Γ u a,
    LR_logically_approximate Δ Γ (Constant (Some (ValueOf u a))) (Constant (Some (ValueOf u a))) (Ty_Builtin (Some (TypeIn u))).
Proof with eauto_LR.
  intros Δ Γ u a.
  unfold LR_logically_approximate.

  split...
  split...

  intros k ρ γ γ' H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Constant. rewrite msubstA_Constant.
  rewrite msubst_Constant. rewrite msubst_Constant.
  rewrite msubstT_TyBuiltin. rewrite msubstT_TyBuiltin.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  exists (Constant (Some (ValueOf u a))), 0.
  split...

  split...
  split...

  left.

  split... intros Hcon. inversion Hcon.
  split... intros Hcon. inversion Hcon.
Qed.
