Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.

Require Import Arith.


Lemma msubst_TyAbs : forall ss bX K t0,
    msubst_term ss (TyAbs bX K t0) = TyAbs bX K (msubst_term ss t0).
Proof. induction ss; intros. - reflexivity. - destruct a. eauto. Qed.

Lemma msubstA_TyAbs : forall ss bX K t0,
    msubstA_term ss (TyAbs bX K t0) = TyAbs bX K (msubstA_term (drop bX ss) t0).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX); eauto. Qed.


Lemma msubstT_TyForall : forall ss bX K T,
    msubstT ss (Ty_Forall bX K T) = Ty_Forall bX K (msubstT (drop bX ss) T).
Proof. induction ss; intros. - reflexivity. - intros. destruct a. simpl. destruct (s =? bX); eauto. Qed.


Lemma compatibility_TyAbs: forall Delta Gamma bX K T e e',
    LR_logically_approximate (bX |-> K; Delta) Gamma e e' T ->
    LR_logically_approximate Delta Gamma (TyAbs bX K e) (TyAbs bX K e') (Ty_Forall bX K T).
Proof with eauto_LR.
  intros Delta Gamma bX K T e e' IH_LR.
  unfold LR_logically_approximate.

  destruct IH_LR as [Htyp__e [Htyp__e' IH__e]].

  split... split... 

  intros k rho env env' ct ck HeqDelta HeqGamma HRD HRG.
  subst.

  autorewrite with RC.

  rewrite msubstA_TyAbs. rewrite msubstA_TyAbs.
  rewrite msubst_TyAbs. rewrite msubst_TyAbs.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  
  eexists. eexists.

  split. {
    eapply eval_value. apply V_TyAbs.
  }

  split... apply skip. 
  split... apply skip.

  eexists. eexists.
  
  split... split...

  intros.

  (*
  eapply IH__e.
  - rewrite mupdate_unfold. reflexivity.
  - reflexivity.
  - split.
    + eapply RD_cons; eauto.
    + apply RG_extend_rho.
      eapply RG_monotone; eauto.
      rewrite <- minus_n_O in Hlt_i.
      apply Nat.lt_le_incl.
      assumption.
  - apply skip.
  - apply skip.
  - apply skip.
  - apply skip.

  Unshelve. all: eauto.
Qed.*)
Admitted.