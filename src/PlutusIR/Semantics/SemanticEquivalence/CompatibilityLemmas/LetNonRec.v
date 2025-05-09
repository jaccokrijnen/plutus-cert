Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
Require Import PlutusCert.Util.
Require Import PlutusCert.Util.Map.
Require Import PlutusCert.Util.Map.Mupdate.

Require Import Arith.
Require Import Coq.Lists.List.

(* TODO: remove duplication in these two *)

Lemma compatibility_LetNonRec_Nil' : forall Delta Gamma t t' Tn,
    Delta |-* Tn : Kind_Base ->
    LR_logically_approximate Delta Gamma t t' Tn ->
    LR_logically_approximate Delta Gamma (Let NonRec nil t) t' Tn.
Proof with eauto_LR.
  intros Delta Gamma t t' Tn Hkind__T IHLR__t.
  unfold LR_logically_approximate.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split...
  {
    econstructor...
    rewrite drop_Δ_nil.
    assumption.
  }
  split...

  intros k rho env env' H_RD H_RG.

  rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil.

  autorewrite with RC.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.
  inversion H3. subst.
  rename j1 into j_1.
  rename H3 into Hev'__e_f.
  rename H1 into Hev''__e_f.

  assert (HRC__t : RC k Tn rho
    (msubst env (msubstA (msyn1 rho) t))
    (msubst env' (msubstA (msyn2 rho) t'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
  destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

  eexists. eexists.

  split...

  split... eapply RV_typable_empty_1...
  split... eapply RV_typable_empty_2...

  eapply RV_condition...
  eapply RV_monotone...
Qed.


(* used in hintdb DSP_compatibility_lemmas, hence it's somewhat strange type (compare to compatibility_LetNonRec_nil')*)
Lemma compatibility_LetNonRec_Nil : forall Delta Gamma t t' Tn,
    forall bsGn,
      map_normalise nil bsGn ->
      Delta |-* Tn : Kind_Base -> (* Richard: Escaping should remove btvbs from Delta, but no btvbs in nil.*)
      LR_logically_approximate Delta (bsGn ++ Gamma) t t' Tn ->
      LR_logically_approximate Delta Gamma (Let NonRec nil t) (Let NonRec nil t') Tn.
Proof with eauto_LR.
  intros Delta Gamma t t' Tn bsGn Hmapnorm__bsGn Hkind__T IHLR__t.
  unfold LR_logically_approximate.

  inversion Hmapnorm__bsGn. subst.
  simpl in IHLR__t.

  destruct IHLR__t as [Htyp__t [Htyp__t' IH__t]].

  split...
  {
    econstructor...
    rewrite drop_Δ_nil.
    assumption.
  }
  split...
  {
    econstructor...
    rewrite drop_Δ_nil.
    assumption.
  }

  intros k rho env env' H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_LetNonRec_nil. rewrite msubstA_LetNonRec_nil.
  rewrite msubst_LetNonRec_nil. rewrite msubst_LetNonRec_nil.

  intros j Hlt__j e_f Hev__e_f.

  inversion Hev__e_f. subst.
  inversion H3. subst.
  rename j1 into j_1.
  rename H3 into Hev'__e_f.
  rename H1 into Hev''__e_f.


  assert (HRC__t : RC k Tn rho
    (msubst env (msubstA (msyn1 rho) t))
    (msubst env' (msubstA (msyn2 rho) t'))
  )...

  apply RC_to_RV with (j := j_1) (e_f := e_f) in HRC__t as temp...
  destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV__t]]].

  eexists. eexists.

  split. eapply E_Let. eapply E_Let_Nil...
  split. eapply RV_typable_empty_1...
  split. eapply RV_typable_empty_2...

  eapply RV_condition...
  eapply RV_monotone...
Qed.
