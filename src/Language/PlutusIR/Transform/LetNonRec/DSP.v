Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.
Require Import PlutusCert.Language.PlutusIR.Transform.LetNonRec.SSP.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Util.

(*
Lemma compatibility_desugar : forall Delta Gamma x Tb eb t eb' t' T Delta' Gamma', 
    Delta |-* Tb : Kind_Base ->
    Delta' = fst (append (binds (TermBind Strict (VarDecl x Tb) eb)) (Delta, Gamma)) ->
    Gamma' = snd (append (binds (TermBind Strict (VarDecl x Tb) eb)) (Delta, Gamma)) ->
    LR_logically_approximate Delta Gamma eb eb' Tb ->
    LR_logically_approximate Delta' Gamma' t t' T ->
    LR_logically_approximate Delta Gamma (Let NonRec (TermBind Strict (VarDecl x Tb) eb :: nil) t) (Apply (LamAbs x Tb t') eb') T.
Proof.
  intros Delta Gamma x Tb eb t eb' t' T Delta' Gamma' Hkind__Tb HeqDelta' HeqGamma' IH_LR__eb IH_LR__t. 
  unfold LR_logically_approximate.

  unfold binds in HeqDelta'.
  unfold binds in HeqGamma'.
  rewrite append_singleton_l in HeqDelta'.
  rewrite append_singleton_l in HeqGamma'.
  simpl in HeqDelta'.
  simpl in HeqGamma'.
  subst. 
  

  split. {
    eapply T_Let; eauto with typing.
    - eapply W_ConsB_NonRec.
      all: eauto with typing.
      apply W_Term. 
      all: eauto with typing.
      apply IH_LR__eb.
    - simpl.
      unfold flatten.
      simpl.
      rewrite append_emptyContext_r.
      rewrite append_singleton_l.
      apply IH_LR__t.
  }

  split. {
    eapply T_Apply; eauto with typing.
    - eapply T_LamAbs.
      all: eauto with typing.
      apply IH_LR__t.
    - apply IH_LR__eb.
  }

  intros k rho env env' ct ck HeqDelta HeqGamma [H_RD H_RG].
  subst.

  intros e_msa e'_msa e_ms e'_ms.
  intros Hmsa__e_msa Hmsa__e'_msa Hms__e_ms Hms__e'_ms.

  apply msubstA_LetNonRec_cons in Hmsa__e_msa as temp.
  destruct temp as [b_msa [bs_msa [t_msa [Hmsa__b_msa [Hmsa__eih_msa Heq]]]]].
  subst.

  apply msubstA_TermBind in Hmsa__b_msa as temp.
  destruct temp as [eb_msa [Hmsa__eb_msa Heq]].
  subst.

  apply msubstA_LetNonRec_nil in Hmsa__eih_msa as temp.
  destruct temp as [t_msa__temp [Hms__t_msa Heq]].
  inversion Heq. symmetry in H1. subst. clear Heq.

  apply msubstA_Apply in Hmsa__e'_msa as temp.
  destruct temp as [t1' [eb'_msa [Hmsa__t1' [Hmsa__eb'_msa Heq]]]].
  subst.

  apply msubstA_LamAbs in Hmsa__t1' as temp.
  destruct temp as [t'_msa [ Hmsa__t'_msa Heq]].
  subst.

  apply msubst_LetNonRec_cons in Hms__e_ms as temp.
  destruct temp as [b_ms [bs_ms [t_ms [Hms__b_ms [Hms__eih_ms Heq]]]]].
  subst.

  apply msubst_TermBind in Hms__b_ms as temp.
  destruct temp as [eb_ms [Hms__eb_ms Heq]].
  subst.

  apply msubst_LetNonRec_nil in Hms__eih_ms as temp.
  destruct temp as [t_ms__temp [Hms__t_ms Heq]].
  inversion Heq. symmetry in H1. subst. clear Heq.
  
  apply msubst_Apply in Hms__e'_ms as temp.
  destruct temp as [t1' [eb'_ms [Hms__t1' [Hms__eb'_ms Heq]]]].
  subst.

  apply msubst_LamAbs in Hms__t1' as temp.
  destruct temp as [t'_ms [ Hms__t'_ms Heq]].
  subst.

  autorewrite with RC.

  split. {
    replace emptyContext with (@ empty Kind, mupd (msyn1 rho) empty).
    - eapply msubst_preserves_typing_1; eauto.
      eapply msubstA_preserves_typing_1; eauto.
      eapply T_Let; eauto.
      + eapply W_ConsB_NonRec; eauto with typing.
        eapply W_Term; eauto with typing.
        apply IH_LR__eb.
      + simpl.
        unfold flatten.
        simpl.
        rewrite append_emptyContext_r.
        rewrite append_singleton_l.
        eapply IH_LR__t.
    - rewrite mupd_empty. reflexivity.
  }

  split. {
    replace emptyContext with (@ empty Kind, mupd (msyn2 rho) empty).
    - eapply msubst_preserves_typing_2; eauto.
      eapply msubstA_preserves_typing_2; eauto.
      eapply T_Apply; eauto.
      + eapply T_LamAbs; eauto.
        eapply IH_LR__t.
      + eapply IH_LR__eb.
    - rewrite mupd_empty. reflexivity.
  }

  intros j Hlt__j e_f Hev__e_f.
  apply inspect_eval__LetNonRec_cons in Hev__e_f as temp.
  destruct temp as [j_1 [eb_f [Hev__eb_f [Hle__j_1 [bs0 [t0 [Hs [j_2 [Hev'__e_f Heq__j]]]]]]]]].
  inversion Hs. subst.
  apply inspect_eval__LetNonRec_nil in Hev'__e_f as temp.
  destruct temp as [j_3 [Hev''__e_f Heq__j_2]].
  subst.

  (* eb *)
  unfold LR_logically_approximate in IH_LR__eb.
  destruct IH_LR__eb as [_ [_ IH_LR__eb]].
  assert (HRC__eb : RC k Tb rho eb_ms eb'_ms) by eauto.

  autorewrite with RC in HRC__eb.

  destruct HRC__eb as [_ [_ HRC__eb]].
  assert (Hlt__j_1 : j_1 < k) by apply skip.
  eapply HRC__eb in Hlt__j_1 as H; eauto.

  destruct H as [eb'_f [j'_1 [Hev__eb'_f H]]].
  clear H HRC__eb. (* DANGER *)


  (* t *)
  unfold LR_logically_approximate in IH_LR__t.
  destruct IH_LR__t as [_ [_ IH_LR__t]].
  assert (HRC__t : RC k T rho t_ms t'_ms). {
    eapply IH_LR__t.
    - reflexivity.
    - rewrite mupdate_unfold.
      reflexivity.
    - apply skip.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
  }

  autorewrite with RC in HRC__t.

  destruct HRC__t as [_ [_ HRC__t]].
  assert (Hlt__j_3 : j_3 < k) by apply skip.
  eapply HRC__t in Hlt__j_3 as H0; eauto.

Admitted.

Definition P_has_type ctx e T := 
  forall e',
    CNR_Term e e' ->
    LR_logically_approximate (fst ctx) (snd ctx) e e' T.

Definition P_constructor_well_formed ctx c := ctx |-ok_c c.

Definition P_bindings_well_formed_nonrec ctx bs := 
  forall bs',
    Congruence.Cong_Bindings CNR_Term bs bs' ->
    LR_logically_approximate_bindings_nonrec (fst ctx) (snd ctx) bs bs'.

Definition P_bindings_well_formed_rec ctx bs1 := ctx |-oks_r bs1.

Definition P_binding_well_formed ctx b := 
  (
    forall b',
      Congruence.Cong_Binding CNR_Term b b' ->
      LR_logically_approximate_binding (fst ctx) (snd ctx) b b'
  ) /\ (
    forall fb' t t' T Delta' Gamma',
      CNR_Binding b fb' ->
      Delta' = fst (append (binds b) (fst ctx, snd ctx)) ->
      Gamma' = snd (append (binds b) (fst ctx, snd ctx)) ->
      LR_logically_approximate Delta' Gamma' t t' T ->
      LR_logically_approximate (fst ctx) (snd ctx) (Let NonRec (b :: nil) t) (fb' t') T
  ).

#[export] Hint Unfold 
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed : core.

Lemma CNR_Term__DSP : forall ctx e T,
    ctx |-+ e : T ->
    P_has_type ctx e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).

  all : autounfold; intros; subst.
  all : try solve [
    inversion X; subst;
    inversion X0; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    inversion X0; subst;
    inversion X1; subst;
    eauto with DSP_compatibility_lemmas typing
  ].
  all : try solve [
    eauto with typing
  ].
  - inversion X.
    + subst.
      apply skip.
    + subst.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas.
  - apply skip.
  - inversion X. subst. 
    constructor. 
  - inversion X. subst. 
    econstructor.
    all: eauto with DSP_compatibility_lemmas.
    apply H0. eauto. 
    inversion X0. 
    subst. 
    all: eauto.
  - split.
    + intros.
      inversion X. subst. 
      eauto with DSP_compatibility_lemmas.
    + intros.
      inversion X. subst.
      apply H1 in X0.
      eapply compatibility_desugar.
      all: auto.
  - split.
    + intros.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas.
    + intros.
      inversion X0. 
  - split.
    + intros.
      inversion X0. subst.
      eauto with DSP_compatibility_lemmas.
    + intros.
      inversion X0.
Qed.*)