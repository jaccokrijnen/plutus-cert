Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.

Ltac solver := try solve [repeat (econstructor; eauto)].


Lemma uniType__basekinded : forall t A,
  uniType_option t = Some A ->
  |-*_uni t : Kind_Base
.
(* TODO: should hold, property of uniType_option *)
Admitted.

Lemma has_type__basekinded : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    Delta |-* T : Kind_Base.
Proof with (eauto || solver).
  induction 1; intros...
  all: try solve [econstructor; eauto using preservation]...
  all: try solve [eauto using preservation]...
  - (* ADMIT: See end of proof *)
    admit.
  - inversion IHhas_type1...
  - inversion IHhas_type. subst.
    eapply preservation.
    2:{
      apply H2.
    }
    eapply substituteTCA_preserves_kinding...
    eapply preservation...
  - unfold unwrapIFix in H1.
    inversion IHhas_type. subst.
    assert (K = K0) by admit.
    subst.
    eapply preservation in H1; eauto.
    econstructor...
    econstructor...
    econstructor...
    econstructor...
    (* ADMIT: Should follow from uniqnuess property. *)
    admit.
  - (* TODO: keep typing derivation around during induction and use uniType__basekinded *)
    admit.
  - destruct f...
    (* TODO: implement lookupBuiltinType *)

(* ADMIT: This should hold if all types in gamma are base kinded, which should
   be the case since we only but base-kinded types in Gamma in our
   type rules. Needs some additional assumptions for the proof to go through. *)
Admitted.
