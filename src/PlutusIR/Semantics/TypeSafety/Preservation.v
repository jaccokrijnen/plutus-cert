Require Import PlutusCert.PlutusIR.Semantics.Dynamic.Bigstep.
Require Import PlutusCert.PlutusIR.Semantics.Static.Typing.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.UniqueTypes.
Require Import PlutusCert.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.
(* SubstituteT behaves as substituteTCA when substituting closed types *)
Lemma closed__substituteT_CA : 
  forall X U T,
    Ty.closed U ->
    substituteTCA X U T = substituteT X U T.
Proof.
Admitted.

Require Import Coq.Program.Equality.

(* Term language type preservation of closed terms under evaluation/reduction*)
Theorem eval__type_preservation : forall t T v k,
    nil ,, nil |-+ t : T ->
    t =[k]=> v ->
    nil ,, nil |-+ v : T.
Proof.
    intros t T v k Ht Hbs.
    generalize dependent T.
    induction Hbs; intros.
    - (* E_LamAbs *)
      exact Ht.
    - (* E_Apply *)
      apply IHHbs3.
      dependent destruction Ht.
      (* inversion Ht as [| |? ? ? ? ? ? Hl Hr | | | | | | | | | ]; subst. *)
      apply IHHbs1 in Ht1.
      inversion Ht1; subst.
      apply substitution_preserves_typing__Term with (U := T1n) (Un := T1n).
      + auto. 
      + apply normalisation__stable'__normal.
        eapply normalise_to_normal; eauto.
      + apply IHHbs2; auto.
    - (* E_TyAbs *)
      exact Ht.
    - (* E_TyInst *)
      apply IHHbs2.
      inversion Ht; subst.
      apply IHHbs1 in H2.
      inversion H2; subst.
      apply substA_preserves_typing__Term__value with (T := T1n) (K := K2).
      + auto.
      + auto.
      + assert ((substituteTCA X0 T2n T1n) = (substituteT X0 T2n T1n)).
        {
          apply closed__substituteT_CA.
          auto.
          (* By T2 well-kinded in empty environment
            and normalise preserves kinding *)
          admit.
        }
        rewrite H in H9.

        auto.
        subst.
        auto.
         (* relation of normalise and substituteT
        *)
        admit.
    - (* E_IWrap *)
      inversion Ht; subst.
      eapply T_IWrap; eauto. (* Through IHHbs*)
    - (* E_Unwrap *)
      inversion Ht; subst.
      apply IHHbs in H1.
      inversion H1; subst.
      assert (K0 = K).
      {
        apply (TypeLanguage.Preservation.preservation _ _ _ _ H7) in H10.
        eapply unique_kinds; eauto.
      }
      subst.
      apply (normalisation__deterministic _ _ _ H5) in H13.
      subst.
      auto.
    - (* E_Constant*)
      exact Ht.
    - (* E_Constr_nil *)
      exact Ht.
    - (* E_Constr_cons *)
      
      admit.
      (* TODO: No typing rules for constr?*)
    - (* E_Builtin *)
      exact Ht.
    - (* E_Apply_Builtin_Partial *)
      inversion Ht; subst.
      inversion H0; subst.
      + admit.
      + (* Hmm need some induction *)
        admit.
      + (* Some induction *)
        admit.
    - (* E_TyInst_Builtin_Partial *)
      admit.
    - (* E_Apply_Builtin_Full *)
      admit.
    - (* E_TyInst_Builtin_Full *)
      admit.
    - (* E_Error *)
      exact Ht.
    - (* E_Error_Apply1 *)

      (* TODO: Error rule was changed to allow
        type checking completeness to go through,
        but that does no longer work for 
        preservation now.
        *)

      inversion Ht; subst.
      
      apply IHHbs in H4.
      

Admitted.