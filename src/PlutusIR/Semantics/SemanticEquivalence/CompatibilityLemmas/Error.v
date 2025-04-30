Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

Require Import Arith.



Lemma compatibility_Error: forall Delta Gamma S Sn,
    Delta |-* S : Kind_Base ->
    normalise S Sn ->
    LR_logically_approximate Delta Gamma (Error S) (Error S) Sn.
Proof with eauto_LR.
  intros Delta Gamma S Sn Hnorm Hkind__S.
  unfold LR_logically_approximate.

  split...
  split...

  intros k rho env env' H_RD H_RG.
  subst.

  autorewrite with RC.

  rewrite msubstA_Error. rewrite msubstA_Error.
  rewrite msubst_Error. rewrite msubst_Error.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f. subst.

  exists (Error (msubstT (msyn2 rho) S)).
  exists 0.

  split. eapply E_Error...

  split. {
    eapply preservation in Hnorm as H...
    eapply closing_preserves_kinding_1 in H as H0...
    eapply strong_normalisation in H0 as H1...
    destruct H1 as [Tn0 H1].
    exists Tn0.
    split...
    (* ADMIT: This is not provable in the current formulation of RC.
      This subproof is not necessary in the new formulation of RC: R. 
      *)
    admit.
  }
  split. {
    eapply preservation in Hnorm as H...
    eapply closing_preserves_kinding_2 in H as H0...
    eapply strong_normalisation in H0 as H1...
    destruct H1 as [Tn0 H1].
    exists Tn0.
    split...
    (* ADMIT: This is not provable in the current formulation of RC.
      This subproof is not necessary in the new formulation of RC: R. 
      *)
    admit.
  }

  right.
  split... econstructor.
  split...
Admitted.
