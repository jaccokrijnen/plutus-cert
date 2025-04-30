Require Import PlutusCert.PlutusIR.Semantics.Dynamic.
Require Import PlutusCert.PlutusIR.Semantics.Static.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.BaseKindedness.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.StrongNormalisation.
Require Import PlutusCert.PlutusIR.Semantics.TypeSafety.TypeLanguage.Preservation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.LogicalRelation.Monotonicity.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Auto.
Require Import PlutusCert.PlutusIR.Semantics.SemanticEquivalence.Multisubstitution.Congruence.
From PlutusCert Require Import Util.Tactics.

From Coq Require Import Lia.
From Coq Require Import Arith.
From Coq Require Import List.
Require Import Coq.Program.Equality.
Import ListNotations.
Import PlutusNotations.

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
    rename j3 into j_3.

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

      admit.
      (*
      apply Hfe with (i := k - j_1 - j_2 - 1) in HRV2 as HRC0...

      assert (k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
      rewrite H.
      clear H.

      apply RC_to_RV with (j := j_3) (e_f := e_f) in HRC0 as temp...
      destruct temp as [e'_f [j'_3 [Hev__e'_f HRV0]]].

      assert (~ is_error e'_f2). {
        apply RV_error in HRV2.
        destruct HRV2.
          - destruct H. assumption.
          - destruct H. contradiction.
          - lia.
        }
      admit.
        *)
    + destruct temp as [Herr Herr'].
      inversion Herr.

  - (* E_Apply_Builtin_Full *)
    admit.
  - (* E_Builtin_Apply_Partial *)

    specialize (IH1 _ _ _ _ H_RD H_RG).
    specialize (IH2 _ _ _ _ H_RD H_RG).
    clear H_RG H_RD.

    admit.
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
        admit.
        (* ADMIT: This is not provable in the current formulation of RC.
          This subproof is not necessary in the new formulation of RC: R. 
         *)
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
        admit.
        (* ADMIT: This is not provable in the current formulation of RC.
          This subproof is not necessary in the new formulation of RC: R. 
         *)
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
        admit.
        (* ADMIT: This is not provable in the current formulation of RC.
          This subproof is not necessary in the new formulation of RC: R. 
         *)
      }

      split. {
        apply has_type__basekinded in Htyp__e1.
        inversion Htyp__e1. subst.
        eapply closing_preserves_kinding_2 in H6...
        apply strong_normalisation in H6 as H7.
        destruct H7.
        exists x.
        split...
        (* ADMIT: This is not provable in the current formulation of RC.
          This subproof is not necessary in the new formulation of RC: R. 
         *)
        admit.
      }

      right...
Admitted.



Ltac eval_deterministic :=
  match goal with
    | H  : ?e =[ _ ]=> ?r
    , H' : ?e =[ _ ]=> ?r'
    |- _ => assert (r = r') by
     eauto using eval__deterministic_result
  end
.

(*
HRV1 : V (k - j_1) <{ T1 → T2 }> ρ <{ λ x :: T, t0 }> r1'
HRV2 : V (k - j_1 - j_2) T1 ρ r2 r2'
*)

(*
(* Related arguments go to related results
*)
Lemma RV_apply {j T1 T2 Δ ρ f f' k v v'} i :
  RD Δ ρ ->
  V j <{ T1 → T2 }> ρ f f' ->
  V k T1 ρ v v' ->
  i < j ->
  i <= k ->
    C i T2 ρ <{ f ⋅ v }> <{ f' ⋅ v' }>.
Proof with eauto_LR.
  intros H_RD H_V_f H_V_v H_j H_k.
  apply V_functional_extensionality with (k := i) (T2 := T2) (v := v) (v' := v') in H_V_f.
  - try assumption.
  split; try assumption.
  (* prepare argument *)
  apply V_monotone with (i := i) (Δ := Δ) in H_V_v...
Qed.
*)

(* There should be a lemma that can compute a new step-index for the result *)
Lemma RV_apply_min {j T1 T2 Δ ρ f f' k v v'} :
  RD Δ ρ ->
  V j <{ T1 → T2 }> ρ f f' ->
  V k T1 ρ v v' ->
  exists (i : nat) (x : binderName) (b b' : term) (T1v T1v' : ty),
    f = <{ λ x :: T1v, b }> /\
    f' = <{ λ x :: T1v', b' }> /\
    C (j - i) T2 ρ <{ [x := v] b }> <{ [x := v'] b' }>.
Proof.
  intros D_Δ V_f V_v.
  destruct (lt_dec k j).
  - (* k < j *)
    exists k.
      admit.
  - admit.
Abort.

Ltac use_RC :=
  match goal with
  | H : C ?k ?T ?ρ ?e1 ?e2
  , Hev : ?e1 =[ ?i ]=> ?v
  |- _ =>
    autorewrite with R in H;
    apply H in Hev as [ ? [ ? [? ?]]];
    clear H;

    idtac
  end
.


Lemma use_approx {Δ ρ Γ γ γ' e e' T }:
  approx Δ Γ e e' T ->
  forall k,
  D Δ ρ ->
  G ρ k Γ γ γ' ->
  C k T ρ (close γ (msyn1 ρ) e) (close γ' (msyn2 ρ) e')
.
Proof.
  unfold approx.
  intros H k H_RD H_RG.
  destruct H as [_ [_ H]].
  auto.
Qed.

Ltac use_approx H_approx k H_RC :=
match type of H_approx with
| approx ?Δ ?Γ _ _ _ =>
  match goal with
  | H_RD : D Δ _
  , H_RG : G _ k Γ _ _
  |- _ => assert (H_RC := use_approx H_approx k H_RD H_RG)
  end
end
.

Ltac RV_apply H_V_f H_V_v i :=
  let H := fresh "tmp" in
  assert (H := H_V_v)
.


Ltac RV_no_error H HR :=
  destruct H as [HR | [H_err H_err'] ];
  try solve [inversion H_err; inversion H_err'];
  try solve [contradiction]
.

Lemma value__Ty_Fun {v T1 T2} :
  value v ->
  [] ,, [] |-+ v : <{ T1 → T2 }>  ->
  (exists x T t,  v = LamAbs x T t) \/ (exists f, args_len v < arity f /\ applied f v)
.
Proof.
  intros H_val H_ty.
  inversion H_val; try solve [inversion H_ty; subst; discriminate].
  - eauto.
  - eauto.
Qed.

Lemma V__Ty_Fun_r {i T1 T2 ρ v v'} :
  V i <{ T1 → T2 }> ρ v v' ->
  (exists x T t,  v' = LamAbs x T t) \/ (exists f , args_len v' < arity f /\ applied f v')
.
Proof.
  intros HV.
  assert (exists T1n T2n, [] ,, [] |-+ v' : <{ T1n → T2n }>).
  {
    apply V_typable_empty_2 in HV as [T' [Hnorm Hty]].
    rewrite msubstT_TyFun in Hnorm.
    inversion Hnorm; subst.
    eauto.
  }
  destruct_hypos.
  eapply value__Ty_Fun.
  - eauto using V_value_2.
  - apply H.
Qed.


Lemma beta__app {x v t k r} T :
  value v ->
  <{ [x := v] t        }> =[ k ]=> r <->
  <{ (λ x :: T , t) ⋅ v}> =[ 1 + k ]=> r
.
Proof.
  intros H_val.
  split.
  - intros H_beta.
    eapply E_Apply; try eauto using eval_value; lia.
  - intros H_app.
    inversion H_app.
    + inversion H2; subst.
      specialize (eval_value _ H_val) as H_e_v.
      assert (H_det : v = v2 /\ 0 = j2) by (eapply eval__deterministic; eauto).
      destruct H_det.
      subst v2.
      subst j2.
      assert (j0 = k) by lia.
      subst j0.
      assumption.
    + inversion H2; subst.
      inversion H3.
    + inversion H2; subst.
      inversion H3.
    + inversion H4; subst.
    + 
      specialize (eval_value _ H_val) as H_e_v.
      assert (H_det : v = Error T0 /\ 0 = j2) by (eapply eval__deterministic; eauto).
      destruct H_det.
      subst v.
      subst t2.
      subst r.
      inversion H_val.
      inversion H2.
Qed.

Lemma compat_Apply Δ Γ e1 e2 e1' e2' T1 T2 :
    approx Δ Γ e1 e1' <{T1 → T2}> ->
    approx Δ Γ e2 e2' T1 ->
    approx Δ Γ <{e1 ⋅ e2}> <{e1' ⋅ e2'}> T2.
Proof with eauto_LR.
  intros IH_LR1 IH_LR2.

  split... admit. (* typing *)
  split... admit. (* typing *)

  intros k ρ γ γ' H_RD H_RG.

  autorewrite with R.
  autorewrite with multi_subst.

  intros j Hlt__j r Hev__app.

  use_approx IH_LR1 k
    C_e1.
  remember (close γ (msyn1 ρ) e1) as c_e1.
  remember (close γ' (msyn2 ρ) e1') as c_e1'.

  use_approx IH_LR2 k
    C_e2.
  remember (close γ (msyn1 ρ) e2) as c_e2.
  remember (close γ' (msyn2 ρ) e2') as c_e2'.

  inversion Hev__app; subst.

  - (* E_Apply *)

    run_C C_e1
      r1' j1' E_e1' R_e1...
    RV_no_error R_e1 V_e1.

    run_C C_e2
      v2' j2' E_e2' R_e2...
    RV_no_error R_e2 V_e2.

    (* Lower the step-index of e2 *)
    apply V_monotone with (i := k - (j1 + j2 + 1)) (Δ := Δ) in V_e2...

    assert (H_lt : k - (j1 + j2 + 1) < k - j1) by lia.

    (* Related arguments go to related values *)
    specialize (V_functional_extensionality H_lt V_e1 V_e2) as [C_app _].
    specialize (C_app x T t0 eq_refl).

    run_C C_app
      r' j' E_app' R_app...

    (* is r1' a lambda or a partially applied builtin? *)
    destruct (V__Ty_Fun_r V_e1) as [ | [f [H_arity H_applied]]].
    + (* it's a lambda *)
        destruct_hypos.
        subst r1'.
        eexists. eexists.
        split.
        (* eval *)
        * eapply E_Apply; try eauto.
          all: admit. (* by inversion on E_app' *)
        * assert ((k - (j1 + j2 + 1 + j3)) = (k - (j1 + j2 + 1) - j3)) by lia.
          rewrite H.
          apply R_app.
    + (*it's a partially applied built-in*)
      assert ((k - (j1 + j2 + 1 + j3)) = (k - (j1 + j2 + 1) - j3)) by lia.
      rewrite H.
      eexists. eexists.
      split.
      * admit. (* Either E_Apply_Builtin_Full or E_APply_Builtin_Partial based
                * on arity of r' ⋅ v2' *)
      * eassumption.

  - (* E_Apply_Builtin_Partial *)
    admit.
  - (* E_Apply_Builtin_Full *)

    use_approx IH_LR1 k
      H_C_e1.
    remember (close γ (msyn1 ρ) e1) as c_e1.
    remember (close γ' (msyn2 ρ) e1') as c_e1'.

    (*
    assert (H_RG' : G ρ (k - (applied_args c_e1)) Γ γ γ'). {
      assert (H : k - applied_args c_e1 <= k)...
      eauto using G_monotone.
    }
    *)
    use_approx IH_LR2 k
      H_C_e2.

    remember (close γ (msyn1 ρ) e2) as c_e2.
    remember (close γ' (msyn2 ρ) e2') as c_e2'.

    admit.


  - (* E_Error_Apply1 *)

    assert (HRC1 :
      C k (Ty_Fun T1 T2) ρ (close γ (msyn1 ρ) e1) (close γ' (msyn2 ρ) e1')
    ) by admit.
    admit.
  - (* E_Error_Apply2 *)
    admit.
Admitted.
