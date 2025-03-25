Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Coq.Lists.List.



Lemma msubst_DatatypeBind : forall ss X YKs matchFunc cs,
    msubst_b ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc cs).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. eauto.
Qed.

Lemma msubstA_DatatypeBind : forall ss X YKs matchFunc cs,
    msubstA_b ss (DatatypeBind (Datatype X YKs matchFunc cs)) = DatatypeBind (Datatype X YKs matchFunc (msubstA_cs ss cs)).
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. simpl. eauto.
Qed.


Lemma append_flatten : forall {X : Type} (m : list (string * X)) x l,
    (flatten (x :: l)) ++ m = (flatten l) ++ (x ++ m).
Proof.
  intros.
  unfold flatten.
  simpl.
  rewrite List.concat_app.
  simpl.
  rewrite List.app_nil_r.
  rewrite List.app_assoc.
  reflexivity.
Qed.

Lemma map_normalise__app' : forall l1 l1n l2 l2n,
    map_normalise l1 l1n ->
    map_normalise l2 l2n ->
    map_normalise (l1 ++ l2) (l1n ++ l2n).
Proof.
  induction l1; intros.
  - inversion H. subst. simpl. eauto.
  - inversion H. subst. simpl. econstructor. eauto. eauto.
Qed.


Lemma compatibility_DatatypeBind : forall Delta Gamma X YKs cs matchFunc Delta' b b' bs bs' t t' Tn,
    Delta' = rev (map fromDecl YKs) ++ Delta  ->
    (forall c, In c cs -> Delta' |-ok_c c : (constrLastTyExpected (Datatype X YKs matchFunc cs))) ->
    forall Delta_ih Gamma_ih bsGn,
      b = DatatypeBind (Datatype X YKs matchFunc cs) ->
      b' = DatatypeBind (Datatype X YKs matchFunc cs) ->
      Delta_ih = binds_Delta b ++ Delta ->
      map_normalise (binds_Gamma b) bsGn ->
      Gamma_ih = bsGn ++ Gamma ->
      LR_logically_approximate Delta_ih Gamma_ih (Let NonRec bs t) (Let NonRec bs' t') Tn ->
      LR_logically_approximate Delta Gamma (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t') Tn.
Proof with eauto_LR.
  intros Delta Gamma X YKs cs matchFunc Delta' b b' bs bs' t t' Tn.
  intros Heq__Delta' Hok__cs.
  intros Delta_ih Gamma_ih bsGn.
  intros Heq__b Heq__b' Heq__Delta_ih Hmapnorm__bsGn Heq__Gamma_ih IHLR__ih.

  subst.

  destruct IHLR__ih as [Htyp__ih [Htyp__ih' IH__ih]].

  split. {
    inversion Htyp__ih. subst.
    (* rewrite <- append_flatten in H7.

    eapply T_Let...
    - unfold flatten.
      simpl.
      simpl in Hmapnorm__bsGn.
      rewrite List.concat_app.
      eapply map_normalise__app'...
      (* ADMIT: Should hold since map_normalise is total for well-kinded types. *)
      admit.
    - econstructor...
      econstructor...
      all: admit.
      (* ADMIT: Add NoDup and well-kinded assumptions from W_Data as arguments (assumptions)
      * to this lemma *)
    - rewrite List.app_assoc in H7. eapply H7.
    - ADMIT: Should follow from uniqueness property. *)
      admit.
  }

  split. {
    (* inversion Htyp__ih'. subst.
    rewrite <- append_flatten in H7.

    eapply T_Let...
    - unfold flatten.
      simpl.
      simpl in Hmapnorm__bsGn.
      rewrite List.concat_app.
      eapply map_normalise__app'...
      (* ADMIT: Should hold since map_normalise is total for well-kinded types. *)
      admit.
    - econstructor...
      econstructor...
      all: admit.
      (* ADMIT: Add NoDup and well-kinded assumptions from W_Data as arguments (assumptions)
      * to this lemma *)
    - rewrite List.app_assoc in H7. eapply H7.
    - ADMIT: Should follow from uniqueness property. *)
      admit.
  }

  intros k rho env env' HRD HRG.
  subst.

  rewrite msubstA_LetNonRec.
  rewrite msubstA_BindingsNonRec_cons.
  rewrite msubstA_DatatypeBind.
  rewrite msubst_LetNonRec.
  rewrite msubst_bnr_cons.
  rewrite msubst_DatatypeBind.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  clear Hev__e_f. rename H3 into Hev__e_f.
  inversion Hev__e_f; subst.
(* ADMIT: Proof contains admits *)
Admitted.
