Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.Constant.


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

Lemma compatibility_Builtin: forall Delta Gamma f,
    LR_logically_approximate Delta Gamma (Builtin f) (Builtin f) (lookupBuiltinTy f).
Proof with eauto_LR.
  intros Delta Gamma f.
  unfold LR_logically_approximate.

  split...
  split...

  intros k rho env env' ct ck HeqDelta HeqGamma H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Builtin. rewrite msubstA_Builtin.
  rewrite msubst_Builtin. rewrite msubst_Builtin.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f.
  - subst.
    exists (ExtBuiltin f nil).
    exists 1.
    
    split. eapply E_Builtin...

    (*
    destruct f.
    + simpl. right.
      eexists. eexists. eexists. eexists.
      split...
      split...
      intros.
      eapply RV_unfolded_to_RV in H.
      autorewrite with RC.
      eapply RV_typable_empty in H as [H1 H2].
      rewrite msubstT_TyBuiltin in H1.
      rewrite msubstT_TyBuiltin in H2.
      rewrite msubstT_TyFun. rewrite msubstT_TyFun.
      rewrite msubstT_TyBuiltin. rewrite msubstT_TyBuiltin.
      split. 
        eapply T_ExtBuiltin; simpl...
        intros p HIn.
        destruct HIn as [Hp | []].
        destruct Hp.
        simpl...
      split. 
        eapply T_ExtBuiltin; simpl...
        intros p HIn.
        destruct HIn as [Hp | []].
        destruct Hp.
        simpl...
      intros.
      eexists. eexists.
      split. eapply E_ExtBuiltinPartiallyApplied...
      right.
      eexists. eexists. eexists. eexists.
      split...
      
      

      exists 

    destruct f; simpl; try discriminate.
    all: try solve [exfalso; auto]. 
    all: right.
    all: eexists; exists nil; eexists; exists nil.
    all: split; eauto.
    all: split; eauto.
    all: intros.
    all: apply RV_unfolded_to_RV in H.
    all: autorewrite with RC.
    all: eapply RV_typable_empty in H as H1...
    all: rewrite msubstT_TyBuiltin in H1.
    all: rewrite msubstT_TyBuiltin in H1.
    all: split.
    all: try split.
    all: try rewrite msubstT_TyFun.
    all: try rewrite msubstT_TyBuiltin.
    all: try rewrite msubstT_TyFun.
    all: try rewrite msubstT_TyBuiltin.
    all: try rewrite msubstT_TyFun.
    all: try rewrite msubstT_TyBuiltin.
    all: try eapply T_ExtBuiltin...
    all: simpl...
    all: try solve  [intros p HIn; destruct HIn as [Hp | []]; destruct Hp; eapply H1].  
    all: intros j_0 Hlt__j_0 e_f0 Hev__e_f0.
    all: inversion Hev__e_f0; subst.
    all: try solve [simpl in H4; discriminate].
    all: eexists; eexists.
    all: split; try econstructor...
    all: eexists; eexists; eexists; eexists.
     econstructor...
    all: try solve [eexists; eexists; econstructor; eauto].
      eexists; eexists; eexists; eexists; eauto].
    all: try solve [exfalso; eapply H0; eauto].

    + apply skip.
    + 
    all: try solve [simpl in H6; exfalso; eapply PeanoNat.Nat.lt_irrefl; eauto].
    all: simpl...
    all: try solve [intros j Hlt__j ]
    
    
    
    eauto; destruct H10; eauto ]. eauto...
    all: split...
    + eapply T_ExtBuiltin...
      * simpl...
      * reflexivity.
      * simpl.
        intros.
        destruct H2...
        destruct H2.
        simpl.
        rewrite msubstT_TyBuiltin in H1.
        apply H1.
      * simpl.
        rewrite msubstT_TyFun.
        rewrite msubstT_TyBuiltin.
        reflexivity.
    +*)
Admitted.