Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.

From Coq Require Import Lia.
From Coq Require Import Arith.
From Coq Require Import List.
Require Import Coq.Program.Equality.
Import ListNotations.
Import PlutusNotations.

Lemma fully_applied__arg_value : forall s v,
  fully_applied (Apply s v) -> v =[0]=> v.
Admitted.

Lemma eta_expand__LamAbs_TyAbs : forall f,
  (exists x T t, eta_expand f = LamAbs x T t) \/
  (exists X K t, eta_expand f = TyAbs X K t).
Proof.
  destruct f; cbv;
    try (solve [left; repeat eexists]).
  right; repeat eexists.
Qed.

Lemma fully_applied__Apply t v :
  fully_applied <{ t ⋅ v }> ->
    exists i x T s,
      t =[i]=> LamAbs x T s
      /\ <{ [v / x] t }> = <{ t ⋅ v }>
.
Admitted.

(*
In a round-about way, a fully applied built-in can also be evaluated by first evaluating its
partial application without the final argument (which will result in a lambda). And then evaluating
in the usual way. Compare for example:

  ------------ E_Builtin (direct, using operational semantics)
  (+) 2 3 => 5

and

  (+) 2 => \x. (+) 2 x
  3     => 3
  -------------------- E_Builtin_partial (derived rule)
  (+) 2 3 => 5

E_Builtin_partial is a "derived" rule, and implemented in terms of a single beta
reduction and then using the standard E_Builtin rule.

*)
Lemma E_Builtin_partial : forall s v i x T t w j,
  fully_applied <{s ⋅ v}>
  -> s =[i]=> LamAbs x T t
  -> <{ [v / x] t }> =[j]=> w
  -> <{ s ⋅ v }> =[i + 1 + j]=> w
.
Proof.
Admitted.

Axiom dec_fully_applied : forall t, {fully_applied t} + {~(fully_applied t)}.


(*
Lemma fully_applied__RC k s t s' t' :
  RC k <{ T1 → T2 }> rho s s'
  RC k <{ T1 }> rho t t'
  fully_applied <{ s ⋅ t }>
  fully_applied <{ s' ⋅ t' }>
.
*)



(* Notation for closing substitutions *)
Notation close γ ρ t := (msubst γ (msubstA ρ t)).

Lemma compatibility_Apply : forall Delta Gamma e1 e2 e1' e2' T1n T2n,
    LR_logically_approximate Delta Gamma e1 e1' (Ty_Fun T1n T2n) ->
    LR_logically_approximate Delta Gamma e2 e2' T1n ->
    LR_logically_approximate Delta Gamma (Apply e1 e2) (Apply e1' e2') T2n.
Proof with eauto_LR.
  intros Delta Gamma e1 e2 e1' e2' T1 T2 IH_LR1 IH_LR2.
  unfold LR_logically_approximate.

  destruct IH_LR1 as [Htyp__e1 [Htyp__e1' IH1]].
  destruct IH_LR2 as [Htyp__e2 [Htyp__e2' IH2]].

  split...
  split...

  intros k rho env env' H_RD H_RG.
  subst.

  autorewrite with RC.
  autorewrite with multi_subst.

  intros j Hlt__j e_f Hev__e_f.
  inversion Hev__e_f; subst.
  - (* E_Apply *)
    rename v2 into e_f2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j0 into j_3.

    assert (HRC1 :
      RC k (Ty_Fun T1 T2) rho
        (msubst env (msubstA (msyn1 rho) e1))
        (msubst env' (msubstA (msyn2 rho) e1'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := LamAbs x T t0) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].



    assert (k - j_1 <= k)...
    assert (HRC2 :
      RC (k - j_1) T1 rho
        (msubst env (msubstA (msyn1 rho) e2))
        (msubst env' (msubstA (msyn2 rho) e2'))
    ) by eauto using RG_monotone.
    clear H.

    apply RC_to_RV  with (j := j_2) (e_f := e_f2) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_functional_extensionality in HRV1 as temp...

    destruct temp as [temp | temp].
    + destruct temp as [Hnerr [Hnerr' temp]].
      destruct temp as [x0 [e_body [e'_body [T1a [T1'a [Heq [Heq' Hfe]]]]]]].
      inversion Heq. subst. clear Heq.

      apply RV_monotone with (i := k - j_1 - j_2 - 1) (ck := Delta)  in HRV2...

      apply Hfe with (i := k - j_1 - j_2 - 1) in HRV2 as HRC0...

      assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
      rewrite H.
      clear H.

      apply RC_to_RV with (j := j_3) (e_f := e_f) in HRC0 as temp...
      destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

      match goal with | |- exists _ _, eval ?t _ _ /\ _ => destruct (dec_fully_applied t) end.
      (* TODO: fix duplication in branches *)
      {
        eexists. eexists.
        split.
        { eapply E_Builtin_partial...
          apply fully_applied__arg_value in f .
          assert (H : close env' (msyn2 rho) e2' = e'_f2 /\ 0 = j'_2). {
            eapply eval__deterministic...
          }
          destruct H. subst.
          eassumption.
        }
        {
          split. eapply RV_typable_empty_1...
          split. eapply RV_typable_empty_2...
          eapply RV_condition...
        }
      }
      {
        {
          eexists. eexists.
          split.
          eapply E_Apply...
          apply RV_error in HRV2... destruct HRV2 as [ [Hnerr0 Hnerr0'] | [Herr0 Herr0']]...
          split. eapply RV_typable_empty_1...
          split. eapply RV_typable_empty_2...
          eapply RV_condition...
        }
      }

      assert (~ is_error e'_f2). {
        apply RV_error in HRV2.
        destruct HRV2.
          - destruct H. assumption.
          - destruct H. contradiction.
          - lia.
        }
      auto.
    + destruct temp as [Herr Herr'].
      inversion Herr.
  - (* E_Builtin *)

    specialize (IH1 _ _ _ _ H_RD H_RG).
    specialize (IH2 _ _ _ _ H_RD H_RG).
    clear H_RG H_RD.

    match goal with | |- exists _ _, eval ?t _ _ /\ _ => destruct (dec_fully_applied t) end.
    { (* fully_applied *)
      eexists. eexists. 
      split.
      {
      (* 
        TODO: By lemma full_applied__Apply, close _ _ e1 and close _ _ e2 both evaluate to lambdas (with
         respectively a property of substituting equality), use
         IH1 with those lambdas and then rewrite the substitution using those equalities.
      *)
      admit.
      }
      { admit.
      (* TODO: typing, similar to E_Apply cases *)
      }
    }
    { (* ~fully_applied *)
      eexists.
      eexists.
      split.
      {
        eapply E_Apply... (* TODO: *)
        { (* from IH1 and fact that fully_applied implies e1 will evaluate to lambda *) admit. }
        { (* from IH2 and fact that fully_aplied implies e2 will be a value *) admit. }
        { (* auto, using existential proven above *) admit. }
        { (* from IH1 *) admit. }
      }
      {
      admit. (* TODO: similar to E_Apply case *)
      }
    }
  
  - (* E_Error_Apply1 *)
    rename j1 into j_1.

    assert (HRC1 :
      RC k (Ty_Fun T1 T2) rho
        (msubst env (msubstA (msyn1 rho) e1))
        (msubst env' (msubstA (msyn2 rho) e1'))
    )...

    apply RC_to_RV with (j := j_1) (e_f := Error T) in HRC1 as temp...
    destruct temp as [e'_f1 [j'_1 [Hev__e'_f1 HRV1]]].

    apply RV_condition in HRV1 as temp...
    destruct temp as [temp | temp].
    + destruct temp. exfalso. apply H. econstructor.
    + destruct temp.
      inversion H0. subst.

      eexists. eexists.
      split. eapply E_Error_Apply1...

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_1 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      right...

  - (* E_Error_Apply2 *)
    rename j2 into j_2.

    assert (HRC2 :
      RC k T1 rho
        (msubst env (msubstA (msyn1 rho) e2))
        (msubst env' (msubstA (msyn2 rho) e2'))
    ) by eauto using RG_monotone.

    apply RC_to_RV  with (j := j_2) (e_f := Error T) in HRC2 as temp...
    destruct temp as [e'_f2 [j'_2 [Hev__e'_f2 HRV2]]].

    apply RV_condition in HRV2 as temp...
    destruct temp as [temp | temp].
    + destruct temp. exfalso. apply H. econstructor.
    + destruct temp.
      inversion H0. subst.

      eexists. eexists.
      split. eapply E_Error_Apply2...

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_1 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
      }

      right...
Admitted.
