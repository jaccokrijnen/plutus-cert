Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.ContextInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.CompatibilityLemmas.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.RelationalModel.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Termination.


(** ** The [R] Lemma *)


Definition P_has_type Gamma e T := 
  LR_logically_approximate (snd Gamma) (fst Gamma) e e T.

Definition P_constructor_well_formed Gamma c := Gamma |-ok_c c.

Definition P_bindings_well_formed_nonrec Gamma bs1 := Gamma |-oks_nr bs1.

Definition P_bindings_well_formed_rec Gamma bs1 := Gamma |-oks_r bs1.

Definition P_binding_well_formed Gamma b1 := Gamma |-ok b1.

Axiom skip : forall P, P.

 (*forall c e1 e2 t1 t2 T,
    (mupdate emptyContext c) |-+ t1 : T ->
    (mupdate emptyContext c) |-+ t2 : T ->
    instantiation c e1 e2 ->
    CNR_Term t1 t2 ->
    forall t1' t2',
      msubst e1 t1 t1' ->
      msubst e2 t2 t2' ->
      R T t1' t2'.*)

Lemma msubst_R : forall Gamma e T,
    Gamma |-+ e : T ->
    P_has_type Gamma e T.
Proof.
  apply has_type__ind with 
    (P := P_has_type)
    (P0 := P_constructor_well_formed)
    (P1 := P_bindings_well_formed_nonrec)
    (P2 := P_bindings_well_formed_rec)
    (P3 := P_binding_well_formed).
  - intros. unfold P_has_type. intros. subst.
    apply skip.
  - intros. unfold P_has_type. intros. subst.
    apply skip.

  - (* T_Var *)
    intros. 
    unfold P_has_type.

    apply compatibility_Var.
    assumption.
    

  - (* T_Forall *)
    intros Gamma X K t0_1 T Htyp_t IH. 
    unfold P_has_type. 

    apply skip.

  - (* T_LamAbs *)
    intros. 
    unfold P_has_type.

  - (* T_Apply *)
    intros Gamma t1 t2 T1 T2 Htyp_t1 IH_t1 Htyp_t2 IH_t2.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t3 t4 Hms_t3 Hms_t4.
    subst.
    
    destruct (msubst_Apply _ _ _ _ Hms_t3) as [t3_1 [t3_2 [Hms_t3_1 [Hms_t3_2 Heq_t3]]]].
    subst.
    destruct (msubst_Apply _ _ _ _ Hms_t4) as [t4_1 [t4_2 [Hms_t4_1 [Hms_t4_2 Heq_t4]]]].
    subst.

    assert (emptyContext |-+ (Apply t3_1 t3_2) : T2) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (Apply t4_1 t4_2) : T2) by eauto using msubst_preserves_typing_2.

    assert (R1: RC k (Ty_Fun T1 T2) t3_1 t4_1) by (eapply IH_t1; eauto; apply skip).
    assert (R2: RC k T1 t3_2 t4_2) by (eapply IH_t2; eauto; apply skip).

    eapply RC_compatibility_Apply; eauto.
  
  - (* T_Constant *)
    intros Gamma u a.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp_t1 _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    apply msubst_Constant in Hmsubst_t2 as Heq2.
    apply msubst_Constant in Hmsubst_t3 as Heq3.
    subst.

    apply RC_compatibility_Constant.
    
  - (* T_Builtin*)
    apply skip.

  - (* T_TyInst *)
    apply skip.

  - (* T_Error *)
    apply skip.

  - (* T_IWrap *)
    intros Gamma F T M K S Hbr Htyp_M IH_M Hkind_T Hkind_F.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    unfold P_has_type in IH_M.

    assert (exists M', msubst e1 M M' /\ t2 = IWrap F T M')
      by eauto using msubst_IWrap.
    destruct H as [M' [Hmsubst_M' Heq_t2]].
    subst.

    assert (exists M'', msubst e2 M M'' /\ t3 = IWrap F T M'')
      by eauto using msubst_IWrap.
    destruct H as [M'' [Hmsubst_M'' Heq_t3]].
    subst.

    assert (emptyContext |-+ (IWrap F T M') : (Ty_IFix F T)) by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (IWrap F T M'') : (Ty_IFix F T)) by eauto using msubst_preserves_typing_2.

    assert (RC k (beta_reduce (unwrapIFix F K T)) M' M''). {
      eapply IH_M; eauto.
    }

    eapply RC_compatibility_IWrap; eauto.
    + inversion H. subst. auto. apply skip. (* TODO *)
    + inversion H0. subst. auto. apply skip. (* TODO *)

  - (* T_Unwrap *)
    intros Gamma M F K T S Htyp_M IH_M Hkind_T Hbr.
    unfold P_has_type.
    intros k c e1 e2 Heq Htyp _ V t2 t3 Hmsubst_t2 Hmsubst_t3.

    unfold P_has_type in IH_M.

    assert (exists M', msubst e1 M M' /\ t2 = Unwrap M')
      by eauto using msubst_Unwrap.
    destruct H as [M' [Hmsubst_M' Heq_t2]].
    subst.

    assert (exists M'', msubst e2 M M'' /\ t3 = Unwrap M'')
      by eauto using msubst_Unwrap.
    destruct H as [M'' [Hmsubst_M'' Heq_t3]].
    subst.

    assert (emptyContext |-+ (Unwrap M') : (beta_reduce (unwrapIFix F K T))) 
      by eauto using msubst_preserves_typing_1.
    assert (emptyContext |-+ (Unwrap M'') : (beta_reduce (unwrapIFix F K T)))
      by eauto using msubst_preserves_typing_2.

    assert (RC k (Ty_IFix F T) M' M''). {
      eapply IH_M; eauto.
    }

    eapply RC_compatibility_Unwrap; eauto.
    + inversion H. subst. apply skip. (* TODO *)

  - 

Abort.