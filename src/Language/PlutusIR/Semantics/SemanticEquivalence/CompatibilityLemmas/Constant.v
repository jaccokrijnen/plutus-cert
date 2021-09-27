Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.

Lemma msubst_Constant : forall ss sv t',
  msubst ss (Constant sv) t' ->
  t' = Constant sv.
Proof.
  induction ss; intros.
  - inversion H. subst. reflexivity.
  - inversion H. subst.
    inversion H2. subst.
    eauto.
Qed.

Lemma msubstA_Constant : forall ss sv t',
  msubstA ss (Constant sv) t' ->
  t' = (Constant sv).
Proof.
  induction ss; intros.
  - inversion H.
    subst.
    reflexivity.
  - inversion H.
    subst.
    inversion H2. 
    subst.
    apply IHss.
    assumption.
Qed.

Lemma msubstTCA_TyConstant : forall ss u T',
    msubstTCA ss (Ty_Builtin (Some (TypeIn u))) T' ->
    T' = Ty_Builtin (Some (TypeIn u)).
Proof.
  induction ss.
  - intros.
    inversion H.
    subst.  
    reflexivity.
  - intros.
    inversion H.
    subst.
    inversion H2.
    subst.
    apply IHss.
    auto.
Qed.

Lemma compatibility_Constant : forall Delta Gamma u a,
    LR_logically_approximate Delta Gamma (Constant (Some (ValueOf u a))) (Constant (Some (ValueOf u a))) (Ty_Builtin (Some (TypeIn u))).
Proof.
  intros Delta Gamma u a.
  unfold LR_logically_approximate.

  split. { apply T_Constant. }
  split. { apply T_Constant. }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_sa e'_sa  e_s e'_s HmsA__e_sa HmsA__e'_sa Hms__e_s Hms__e'_s.
  
  apply msubstA_Constant in HmsA__e_sa.
  apply msubstA_Constant in HmsA__e'_sa.
  subst.
  apply msubst_Constant in Hms__e_s.
  apply msubst_Constant in Hms__e'_s.
  subst.


  autorewrite with RC.

  split. { 
    eexists. 
    split.
    - apply skip.
    - apply T_Constant.  
  }
  split. { 
    eexists. 
    split.
    - apply skip.
    - apply T_Constant.  
  }

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.

  exists (Constant (Some (ValueOf u a))), 0.
  split. { apply eval_value. apply V_Constant. }
  
  intros v v' sv sv' Heq Heq'.
  subst.

  intros Heq0 Heq0'.
  inversion Heq0. inversion Heq0'. subst.

  reflexivity.
Qed.