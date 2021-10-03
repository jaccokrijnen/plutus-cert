Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

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

Lemma compatibility_Constant : forall Delta Gamma u a,
    LR_logically_approximate Delta Gamma (Constant (Some (ValueOf u a))) (Constant (Some (ValueOf u a))) (Ty_Builtin (Some (TypeIn u))).
Proof.
  intros Delta Gamma u a.
  unfold LR_logically_approximate.

  split. { apply T_Constant. }
  split. { apply T_Constant. }

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  rewrite msubstA_Constant.
  rewrite msubstA_Constant.
  rewrite msubst_Constant.
  rewrite msubst_Constant.

  autorewrite with RC.

  split. { rewrite msubstT_TyBuiltin. apply T_Constant. }
  split. { rewrite msubstT_TyBuiltin. apply T_Constant. }

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.

  exists (Constant (Some (ValueOf u a))), 0.
  split. { apply eval_value. apply V_Constant. }

  eauto.
Qed.