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

Lemma msubstA_Constant : forall ss sv,
  msubstA ss (Constant sv) (Constant sv).
Proof.
  induction ss; intros.
  - apply msubstA_nil.
  - destruct a. 
    eapply msubstA_cons.
    + apply SA_Constant.
    + apply IHss.
Qed.

Lemma msubstT_TyConstant : forall ss u,
    msubstT ss (Ty_Builtin (Some (TypeIn u))) = Ty_Builtin (Some (TypeIn u)).
Proof.
  induction ss.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    apply IHss.
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

  intros e_substed e'_substed Hms__e Hms__e'.
  
  apply msubst_Constant in Hms__e as Heq.
  apply msubst_Constant in Hms__e' as Heq'.
  subst.
  clear Hms__e Hms__e'.

  autorewrite with RC.

  split. { 
    exists (Constant (Some (ValueOf u a))).
    split. 
    - apply msubstA_Constant.
    - rewrite msubstT_TyConstant. 
      apply T_Constant. 
  }
  split. { 
    exists (Constant (Some (ValueOf u a))).
    split. 
    - apply msubstA_Constant.
    - rewrite msubstT_TyConstant. 
      apply T_Constant. 
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