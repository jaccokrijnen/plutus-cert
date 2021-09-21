Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.UniqueTypes.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.

Require Import Arith.


Lemma msubst_LamAbs : forall ss x T t0 t',
    closed_env ss ->
    msubst ss (LamAbs x T t0) t' ->
    exists t0', msubst (drop x ss) t0 t0' /\ t' = LamAbs x T t0'.
Proof.
  induction ss.
  - intros. 
    inversion H0. subst.
    exists t0.
    split. 
    + apply msubst_nil.
    + reflexivity. 
  - intros.
    inversion H0. subst.
    rename t'0 into t''.
    destruct H.
    inversion H3.
    + subst.
      simpl.
      rewrite eqb_refl.
      eapply IHss; eauto.
    + subst.
      simpl.
      apply eqb_neq in H10.
      rewrite H10.
      edestruct IHss as [t0'' Hms0']; eauto.
      eexists.
      split.
      -- eapply msubst_cons.
         ++ apply H11.
         ++ apply Hms0'.
      -- destruct Hms0'.
         subst.
         reflexivity.
Qed.

Lemma compatibility_LamAbs : forall Delta Gamma x T1 e e' T2,
    (Gamma, Delta) |-* T1 : Kind_Base ->
    LR_logically_approximate Delta (x |-> T1; Gamma) e e' T2 ->
    LR_logically_approximate Delta Gamma (LamAbs x T1 e) (LamAbs x T1 e') (Ty_Fun T1 T2).
Proof.
  intros Delta Gamma x T1 e e' T2 Hkind__T1 IH_LR.
  unfold LR_logically_approximate.

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_LamAbs. auto. auto.
  }

  split. {
    edestruct IH_LR as [Htyp__e [Htyp__e' H]].
    apply T_LamAbs. auto. auto.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_s e'_s Hms__e_s Hms__e'_s.

  assert (Hcls1 : closed_env env) by (eapply RG_env_closed_1; eauto).
  assert (Hcls2 : closed_env env') by (eapply RG_env_closed_2; eauto).
  destruct (msubst_LamAbs _ _ _ _ _ Hcls1 Hms__e_s) as [e_s0 [Hms__e_s0 Heq]].
  destruct (msubst_LamAbs _ _ _ _ _ Hcls2 Hms__e'_s) as [e'_s0 [Hms__e'_s0 Heq']].
  subst.
  clear Hcls1 Hcls2.

  assert (emptyContext |-+ (LamAbs x T1 e) : (msubstT_rho_syn1 rho (Ty_Fun T1 T2))). {
    destruct IH_LR as [Htyp__e [Htyp__e' H]].
    assert ((mupdate empty ct, mupdate empty ck) |-+ (LamAbs x T1 e) : (Ty_Fun T1 T2)). {
      eapply T_LamAbs; eauto.
    }
    assert ()

    eapply T_LamAbs in Htyp__e.
  }
  assert (emptyContext |-+ (LamAbs x T1 e') : (Ty_Fun T1 T2)).

  unfold P_has_type in IH.

  autorewrite with RC.
  split; auto. split; auto.
  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  exists (LamAbs x T1 t0_3).
  exists 0.
  split. {
    eapply eval_value. apply V_LamAbs.
  }
  intros.
  inversion H1. subst.
  inversion H2. subst.

  assert (msubst ((x', v) :: drop x' e1) t0_1 e_body'). { apply skip. }
  assert (msubst ((x', v') :: drop x' e2) t0_1 e'_body'). { apply skip. }

  eapply IH; eauto.
  + assert (x' |T-> T1; mupdate emptyContext c = mupdate emptyContext ((x', T1) :: drop x' c)). {
      apply skip.
    }
    apply H10.
  + apply V_cons; eauto.
    eapply instantiation_drop.
    apply skip.