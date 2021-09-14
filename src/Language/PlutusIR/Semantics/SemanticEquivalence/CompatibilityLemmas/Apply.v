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

Require Import Arith.

Lemma termination_congr_Apply1 : forall t1 t2 k,
  terminates (Apply t1 t2) k ->
  terminates t1 k.
Proof.
  intros.
  destruct H as [v0 [j [Hlt_j]]].
  inversion Hlt_j.
  - subst.
    exists (LamAbs x T t4).
    exists k1.
    split; auto.
    apply skip.
Admitted.

Lemma termination_congr_Apply2 : forall t1 t2 k,
  terminates (Apply t1 t2) k ->
  terminates t2 k.
Proof. Admitted.

Lemma R_compatibility_Apply : forall k T1 T2 t1_1 t1_2 t2_1 t2_2,
    (terminates (Apply t1_1 t1_2) k \/ ~ terminates (Apply t2_1 t2_2) k) ->
    R k (Ty_Fun T1 T2) t1_1 t2_1 ->
    R k T1 t1_2 t2_2 ->
    R k T2 (Apply t1_1 t1_2) (Apply t2_1 t2_2).
Proof.
  intros k T1 T2 t1_1 t1_2 t2_1 t2_2 Hterm R1 R2.

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

    intros v1_0 j1 Hlt_j1 Hev1. 

    assert (Hterm1: terminates (Apply t1_1 t1_2) k). {
      exists v1_0, j1. auto.
    }
    assert (Hterm_t1_1 : terminates t1_1 k). {
      inversion Hev1; subst; eapply termination_congr_Apply1; eauto.
    }
    assert (Hterm_t1_2 : terminates t1_2 k). {
      inversion Hev1; subst; eapply termination_congr_Apply2; eauto.
    }

    apply R_functional_extensionality in R1 as temp; eauto.
    destruct temp as [v1_1 [v2_1 [j1_1 [j2_1 [Hlt1_1 [Hev1_1 [Hev2_1 Hfe]]]]]]].
    destruct k. {
      apply R_impossible_k in R1; eauto. destruct R1.
    }
Abort.