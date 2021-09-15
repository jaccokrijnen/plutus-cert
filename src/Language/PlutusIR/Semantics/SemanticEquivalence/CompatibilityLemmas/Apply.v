Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.Language.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.
Require Import PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.Named.ContextInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.Preservation.
Require Import PlutusCert.Language.PlutusIR.Semantics.TypeSafety.SubstitutionPreservesTyping.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Def.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Monotonicity.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.ReductionInvariance.
Require Import PlutusCert.Language.PlutusIR.Semantics.SemanticEquivalence.Termination.

Require Import Arith.
Require Import Coq.Logic.Decidable.



Lemma R_compatibility_Apply : forall k T1 T2 t1_1 t1_2 t2_1 t2_2 j v,
    terminates_excl (Apply t1_1 t1_2) j v k ->
    R k (Ty_Fun T1 T2) t1_1 t2_1 ->
    R k T1 t1_2 t2_2 ->
    R k T2 (Apply t1_1 t1_2) (Apply t2_1 t2_2).
Proof.
  intros k T1 T2 t1_1 t1_2 t2_1 t2_2 j v Hterm R1 R2.

  assert (Htyp1 : emptyContext |-+ (Apply t1_1 t1_2) : T2). {
    apply T_Apply with T1.
    - eapply R_typable_empty_1; eauto.
    - eapply R_typable_empty_1; eauto.
  } 
  assert (Htyp2 : emptyContext |-+ (Apply t2_1 t2_2) : T2). {
    apply T_Apply with T1.
    - eapply R_typable_empty_2; eauto.
    - eapply R_typable_empty_2; eauto.
  }

  autorewrite with R.
  
  destruct T2.
  - (* Ty_Var S *)
    split; auto. split; auto.
    apply skip.
  - apply skip.
  - apply skip.
  - apply skip.
  - (* Ty_Builtin *)
    split; auto. split; auto.

    intros.
    apply termination_congr_Apply1 in H as H0.
    destruct H0 as [v1_1 [j1_1 Hterm1_1]].
    destruct Hterm1_1 as [Hev1_1 Hlt1_1] eqn:Hterm1_1'.
    clear Hterm1_1'.

    assert (j1_1 < k) by eauto using le_lt_trans.
    assert (terminates_excl t1_1 j1_1 v1_1 k). {
      eapply terminates__incl_excl in Hterm1_1.
      eapply terminates_excl__monotone; eauto.
    }

    eapply R_functional_extensionality in R1 as temp; eauto. 
    destruct temp as [v2_1 [j2_1 [Hev2_1 Hfe]]].

    assert (exists x T t0, v1_1 = LamAbs x T t0). {
      assert (emptyContext |-+ v1_1 : (Ty_Fun T1 (Ty_Builtin s))). {
        eapply preservation; eauto.
        eapply R_typable_empty_1; eauto.
      }
      apply skip.
    }
    destruct H2 as [x1_0 [T1_0 [t1_0 Heq1_0]]]. subst.

    eapply termination_congr_Apply2 in H as H2; eauto.
    destruct H2 as [v1_2 [j1_2 Hterm1_2]].
    destruct Hterm1_2 as [Hev1_2 Hlt1_2] eqn:Hterm1_2'.
    clear Hterm1_2'.

    assert (k - j1_1 <= k). { apply skip. }
    assert (R (k - j1_1) T1 t1_2 t2_2). {
      eapply R_monotone.
      - reflexivity.
      - reflexivity.
      - apply H2.
      - apply R2.
    }

    assert (exists t1_0', substitute x1_0 v1_2 t1_0 t1_0') by (eapply substitute_models_total_function__Term; eauto).
    destruct H4 as [t1_0' Hsubst1_0].
    eapply termination_congr_Apply3 in H as H4; eauto.
    destruct H4 as [j1_0 [Hterm1_0 Heq]].
    destruct Hterm1_0 as [Hev1_0 Hlt1_0] eqn:Hterm1_0'.
    clear Hterm1_0'.


    assert (exists v2_2 j2_2, t2_2 =[j2_2]=> v2_2). {
      eapply R_evaluable_2.
      apply skip.
      apply skip.
      apply skip.
    }

    destruct H4 as [v2_2 [j2_2 Hev2_2]].

    assert (k - j1_1 - j1_2 - 1 <= k - j1_1). { apply skip. }
    assert (R (k - j1_1 - j1_2 - 1) T1 v1_2 v2_2). {
      eapply R_monotone.
      - reflexivity.
      - reflexivity.
      - apply H4. 
      - eapply eval_preserves_R; eauto. apply skip. 
    }

    assert (k - j1_1 - j1_2 - 1 < k - j1_1). { apply skip. }

    remember (Hfe v1_2 v2_2 (k - j1_1 - j1_2 -1)).
    clear Heqr.
    assert (exists x T t0, v2_1 = LamAbs x T t0). {
      assert (emptyContext |-+ v2_1 : (Ty_Fun T1 (Ty_Builtin s))). {
        eapply preservation; eauto.
        eapply R_typable_empty_2; eauto.
      }
      apply skip.
    }
    destruct H7 as [x2_0 [T2_0 [t2_0 Heq2_0]]]. subst.
    assert (exists t2_0', substitute x2_0 v2_2 t2_0 t2_0') by (eapply substitute_models_total_function__Term; eauto).
    destruct H7 as [t2_0' Hsubst2_0'].
    remember (r x1_0 x2_0 T1_0 T2_0 t1_0 t2_0 t1_0' t2_0').

    assert (R (k - j1_1 - j1_2 - 1) (Ty_Builtin s) t1_0' t2_0'). { apply skip. }

    eapply R_syntactic_equality in H7; eauto. 
    destruct H7.
    destruct H7.
    destruct H7.
Abort.