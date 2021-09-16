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



Lemma R_compatibility_Apply : forall k T1 T2 e1 e2 e1' e2',
    RC k (Ty_Fun T1 T2) e1 e1' ->
    RC k T1 e2 e2' ->
    RC k T2 (Apply e1 e2) (Apply e1' e2').
Proof.
  intros k T1 T2 e1 e2 e1' e2'.
  intros RC1 RC2.

  assert (Htyp : emptyContext |-+ (Apply e1 e2) : T2). {
    apply T_Apply with T1.
    - eapply RC_typable_empty_1; eauto.
    - eapply RC_typable_empty_1; eauto.
  } 
  assert (Htyp' : emptyContext |-+ (Apply e1' e2') : T2). {
    apply T_Apply with T1.
    - eapply RC_typable_empty_2; eauto.
    - eapply RC_typable_empty_2; eauto.
  }

  autorewrite with RC.

  (* First part of the proof *)
  split; auto. split; auto.

  (* Second part of the proof *)

  (** 
      Consider arbitrary j, ef such that 
      # j < k, and
      # Apply e1 e2 =[j]=> e_f 
  *)
  intros j Hlt__j e_f ev__e.

  (** 
      Hence, by inspection of the operational semantics, it follows that there 
      exist j1 and e_f1 such that
      # e1 =[j1]=> e_f1, and
      # j1 <= j
  *)
  assert (temp: exists j1 e_f1, e1 =[j1]=> e_f1 /\ j1 <= j) by eauto using termination_congr_Apply1.
  destruct temp as [j1 [e_f1 [Hev__e1 Hle__j1_j]]].

  (** 
      Instantiate the second conjunct of RC1 with k. ... Instantiate this with j1, e_f1. Note that
      # j1 < k, which follows from j1 <= j and j < k, and
      # e1 =[j1]=> e_f1.
  *)
  assert (Hlt__j1_k : j1 < k) by eauto using Nat.le_lt_trans. 

  autorewrite with RC in RC1.
  destruct RC1 as [_ [_ RC1]].
  remember (RC1 j1 Hlt__j1_k e_f1 Hev__e1) as temp.
  clear Heqtemp. clear RC1. rename temp into RC1.

  (** 
      Hence, there exists e'_f1 (and j'_1) such that
      # e1' =[j'_1]=> e'_f1, and
      # (k - j1, e_f1, e'_f1) \in RV[[T1 -> T2]]
  *)
  destruct RC1 as [e'_f1 [j'_1 [Hev__e1' RV1]]].

  (**
      Hence, 
        e_f1 `equiv` (LamAbs x T1 e_f1__body), and 
        e'_f1 `equiv` (LamAbs x' T1 e'_f1__body).

      TODO: This is not actually true because of the way we handle builtin functions. However,
      I will assume this for now to simplify the proof.
  *)
  assert (temp: exists x e_f11, e_f1 = LamAbs x T1 e_f11). { apply skip. }
  destruct temp as [x [e_f11 Heq]].
  assert (temp: exists x' e'_f11, e'_f1 = LamAbs x' T1 e'_f11). { apply skip. }
  destruct temp as [x' [e'_f11 Heq']].
  
  (**
      Note that 
        Apply e1 e2 -[j1]-> Apply (LamAbs x T1 e_f11) e2 -[j-j1]-> e_f
        
      Hence, by inspection of the operational semantics it follows that thre exist j2 and and e_f2
      such that
      # e2 =[j2]=> e_f2, and
      # j2 <= j - j1
  *)
  assert (temp: exists j2 e_f2, e2 =[j2]=> e_f2 /\ j2 <= j - j1). {
    eapply termination_congr_Apply2; eauto. split; eauto.
  }
  destruct temp as [j2 [e_f2 [Hev__e2 Hle__j2]]].

  (**
      Instantiate the second conjunct of RC2 with (k - j1). 
  *)
  remember RC2 as RC2'. clear HeqRC2'.
  assert (temp: RC (k - j1) T1 e2 e2'). {
    eapply RC_monotone.
    - split. apply Hev__e2. apply skip. (* TODO *)
    - eassumption.
    - apply skip. (* TODO *) 
  }
  clear RC2. rename temp into RC2.

  (** 
      Instantiate this with j2 and e_f2. Note that
      # j2 < k - j1, which follows from j2 <= j - j1 and j < k.
      # e2 =[j2]=> e_f2
  *)
  assert (Hlt__j2_k_j1 : j2 < k - j1). { apply skip. (* TODO *) }
  
  autorewrite with RC in RC2.
  destruct RC2 as [_ [_ RC2]].
  remember (RC2 j2 Hlt__j2_k_j1 e_f2 Hev__e2) as temp.
  clear Heqtemp. clear RC2. rename temp into RC2.

  (**
      Hence, there exists e'_f2 (and j'_2) such that 
      # e2' =[j'_2]=> e'_f2, and
      # (k - j1 - j2, e_f2, e'_f2) \in RV[[T1]]
  *)
  destruct RC2 as [e'_f2 [j'_2 [Hev__e2' _]]].
  assert (RV2: RC (k - j1 - j2) T1 e_f2 e'_f2). {
    apply skip. (* TODO *)
  }

  (** 
      Hence, 
        e_f2 `equiv` v_f2, and
        e'_f2 `equiv` v'_f2. 
        
      NOTE: In other words, e_f2 and e'_f2 are values. 
  *)
  rename e_f2 into v_f2. rename e'_f2 into v'_f2.

  (** 
      Note that 
        Apply e1 e2 
        -[j1]-> 
        Apply (LamAbs x T1 e_f11) e2 
        -[j2]->
        Apply (LamAbs x T1 e_f11) v_f2
        -[1]->
        e_f11 [v_f2 / x]
        -[j3]->
        e_f
      
      and irred(e_f) and j = j1 + j2 + 1 + j3.

      Instantiate the second conjunct of RV1 with k - j1 - j2 -1, v_f2 and v'_f2. Note that
      # k - j1 - j2 - 1 < k - j1, and
      # (k - j1 - j2 -1, v_f2, v'_f2) \in RV[[T1]]
  *)

  (* messy below *)
  assert (Hlt__j1_j2_k_j1 : k - j1 - j2 - 1 < k - j1). { apply skip. (* TODO *) }

  remember (RV1 x e_f11 x' e'_f11 Heq Heq' (k - j1 - j2 - 1) Hlt__j1_j2_k_j1) as temp.
  clear Heqtemp. clear RV1. rename temp into RV1.

  assert (RC (k - j1 - j2 - 1) T1 v_f2 v'_f2). {
    eapply RC_monotone.
    - split. eapply eval_value. eapply eval_to_value. eapply Hev__e2. apply skip. 
    - eassumption.
    - apply skip.
  }

  assert (temp : exists e_f11__substed, substitute x v_f2 e_f11 e_f11__substed). {
    eapply substitute_models_total_function__Term.
  }
  destruct temp as [e_f11__substed Hsubst].
  assert (temp : exists e'_f11__substed, substitute x' v'_f2 e'_f11 e'_f11__substed). {
    eapply substitute_models_total_function__Term.
  }
  destruct temp as [e'_f11__substed Hsubst'].

  assert (RC (k - j1 - j2 - 1) T2 e_f11__substed e'_f11__substed). {
    eapply RV1; eauto.
  }

  autorewrite with RC in H0.
  destruct H0 as [_ [_ H0]].

  assert (exists j0, terminates_incl e_f11__substed j0 e_f (j - j1 - j2 - 1) /\ j = j1 + j2 + 1 + j0). {
    eapply termination_congr_Apply3; eauto. split; eauto. subst. eauto. split; eauto.
  }
  destruct H1 as [j3 H1]. destruct H1. destruct H1.

  assert (j3 < k - j1 - j2 - 1). { apply skip. }
  remember (H0 j3 H4 e_f H1). clear Heqe. destruct e. destruct H5. destruct H5. exists x0, (j'_1 + j'_2 + 1 + x1). split. {
    eapply E_Apply; eauto. subst; eauto.
  }

  destruct T2; eauto.
  all : intros;
    eapply H6; eauto;
    subst.
  - apply skip.
  - apply skip.
  - apply skip.
Qed.