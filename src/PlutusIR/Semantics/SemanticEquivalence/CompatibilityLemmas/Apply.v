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
    exists x T s,
      t =[ applied_args t ]=> LamAbs x T s
      /\ <{ [v / x] s }> = <{ t ⋅ v }>
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



Ltac eval_deterministic :=
  match goal with
    | H  : ?e =[ _ ]=> ?r
    , H' : ?e =[ _ ]=> ?r'
    |- _ => assert (r = r') by
     eauto using eval__deterministic_result
  end
.

(*
HRV1 : R_V (k - j_1) <{ T1 → T2 }> ρ <{ λ x :: T, t0 }> r1'
HRV2 : R_V (k - j_1 - j_2) T1 ρ r2 r2'
*)


Lemma RV_apply {j T1 T2 Δ ρ f f' k v v'} i :
  RD Δ ρ ->
  R_V j <{ T1 → T2 }> ρ f f' ->
  R_V k T1 ρ v v' ->
  i < j ->
  i < k ->
  exists (x : binderName) (b b' : term) (T1v T1v' : ty),
    f = <{ λ x :: T1v, b }> /\
    f' = <{ λ x :: T1v', b' }> /\
    R_C i T2 ρ <{ [ v / x] b }> <{ [v' / x] b' }>.
Proof with eauto_LR.
  intros H_RD H_V_f H_V_v H_j H_k.
  apply R_V_functional_extensionality in H_V_f
    as [ x [ b [ b' [ T1v [T1v' [H_v [H_v' H_ext ]]]]]]].
  exists x, b, b', T1v, T1v'.
  split; try assumption.
  split; try assumption.
  (* prepare argument *)
  apply R_V_monotone with (i := i) (ck := Δ)  in H_V_v...
Qed.




Ltac use_RC :=
  match goal with
  | H : R_C ?k ?T ?ρ ?e1 ?e2
  , Hev : ?e1 =[ ?i ]=> ?v
  |- _ =>
    autorewrite with R in H;
    apply H in Hev as [ ? [ ? [? ?]]];
    clear H;

    idtac
  end
.

Ltac run_RC H_RC r' j' H_eval' H_res':=
  match type of H_RC with
  | R_C ?k ?T ?ρ ?e1 ?e2 =>
    match goal with
    | H : e1 =[ ?i ]=> ?v1 |- _ =>
        let H_temp := fresh "H" in
        assert (H_temp := H_RC);
        autorewrite with R in H_temp;
        assert (H' := H);
        apply H_temp in H' as [r' [j' [H_eval' H_res']]];
        clear H_temp
    | _ =>
      fail 1 "Could not find required hypothesis of type eval"
    end
  end
.

Lemma use_approx {Δ ρ Γ γ γ' e e' T }:
  approx Δ Γ e e' T ->
  forall k,
  RD Δ ρ ->
  R_G ρ k Γ γ γ' ->
  R_C k T ρ (close γ (msyn1 ρ) e) (close γ' (msyn2 ρ) e')
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
  | H_RD : RD Δ _
  , H_RG : R_G _ k Γ _ _
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

Lemma H_fully_applied e1 e2 e1' e2' T1 T2 k Δ ρ:
  RD Δ ρ ->
  fully_applied <{e1 ⋅ e2}> ->
  fully_applied <{e1' ⋅ e2'}> ->
  applied_args <{ e1 ⋅ e2 }> < k -> (* we can make at least applied_args <{e1 ⋅ e2}> steps *)
  R_C k <{ T1 → T2 }> ρ e1 e1' ->
  R_C k T1 ρ e2 e2' ->
  R_C (k - applied_args <{ e1 ⋅ e2 }>) T2 ρ <{e1 ⋅ e2}> <{e1' ⋅ e2'}>
.
Proof.
  intros H_RD H_FA H_FA' H_lt H_RC_e1 H_RC_e2 .
  (* e1 terminates as a lambda *)
  apply fully_applied__Apply in H_FA as [x [T [b [H_ev_e1 H_eq_subst]]]].
  autorewrite with R in H_RC_e1.
  apply H_RC_e1 in H_ev_e1 as [r' [j' [ H_ev H_RV_r ]]]; clear H_RC_e1.
  - destruct H_RV_r as [H_RV_r | [H_err _] ]; [ | inversion H_err].
    apply R_V_functional_extensionality in H_RV_r as [x' [e_body [b' [T3 [T' [H_eq [H_eq_r' H_RV_r']]]]]]].
    subst.
    symmetry in H_eq.
    inversion H_eq; subst; clear H_eq.

    (* Convert R_C to R_V *)
    assert (H_RV_e2 : R_V k T1 ρ e2 e2'). {
      assert (0 < k). autorewrite with applied_args in H_lt; lia.
      assert (value e2). admit.
      assert (value e2'). admit.
      eauto using R_C_values_to_R_V.
    }
    apply R_V_monotone with (i := k - (applied_args <{e1 ⋅ e2}>)) (ck := Δ) in H_RV_e2.
    apply H_RV_r' in H_RV_e2; clear H_RV_r'.
    rewrite H_eq_subst in H_RV_e2. clear H_eq_subst.
    apply fully_applied__Apply in H_FA' as [x' [T'' [b'' [H_ev_e1' H_eq_subst']]]].
    assert (H_e1'_r' := eval__deterministic _ _ _ H_ev _ _ H_ev_e1').
    destruct H_e1'_r' as [H_eq_lam H_eq_args].
    inversion H_eq_lam; subst.
    rewrite H_eq_subst' in H_RV_e2.
    assumption.
all: try solve [eauto | lia].
autorewrite with applied_args in *. lia.
- autorewrite with applied_args in *. lia.
Admitted.


Lemma compat_Apply_builtin Δ Γ e1 e2 e1' e2' T1 T2 :
    fully_applied <{e1 ⋅ e2}> ->
    approx Δ Γ e1 e1' (Ty_Fun T1 T2) ->
    approx Δ Γ e2 e2' T1 ->
    approx Δ Γ (Apply e1 e2) (Apply e1' e2') T2.
Proof.
  intros H_FA H_approx_e1 H_approx_e2.
  unfold approx.
  split; [ admit | split; [admit | ]].

  intros ? ? ? ?.
  intros H_RD H_RG.
  destruct H_approx_e1 as [_ [ _ H_RC_e1]].
  destruct H_approx_e2 as [_ [ _ H_RC_e2]].
Admitted.

Lemma compat_Apply Δ Γ e1 e2 e1' e2' T1 T2 :
    approx Δ Γ e1 e1' (Ty_Fun T1 T2) ->
    approx Δ Γ e2 e2' T1 ->
    approx Δ Γ (Apply e1 e2) (Apply e1' e2') T2.
Proof with eauto_LR.
  intros IH_LR1 IH_LR2.

  (*
  destruct IH_LR1 as [Htyp__e1 [Htyp__e1' IH1]].
  destruct IH_LR2 as [Htyp__e2 [Htyp__e2' IH2]].
  *)

  split...
  admit.
  split...
  admit.

  intros k ρ γ γ' H_RD H_RG.

  autorewrite with R.
  autorewrite with multi_subst.

  intros j Hlt__j r Hev__app.


  inversion Hev__app; subst.
  - (* E_Apply *)
    rename v2 into r2.
    rename j1 into j_1.
    rename j2 into j_2.
    rename j0 into j_3.


    (* Use IH1 with k steps *)
    use_approx IH_LR1 k
      H_C_e1.
    run_RC H_C_e1
      r1' j_1' H_ev__e1' H_V_f...
    clear H_C_e1.
    RV_no_error H_V_f H_V_f.

    (* Use IH2 with k - j1 steps *)
    assert (H_RG' : R_G ρ (k - j_1) Γ γ γ'). {
      assert (H : k - j_1 <= k)...
      eauto using R_G_monotone.
    }
    use_approx IH_LR2 (k - j_1)
      H_C_e2.
    run_RC H_C_e2
      r2' j_2' H_ev__e2' H_V_2...
    clear H_C_e2.
    RV_no_error H_V_2 H_V_2.

    (* Related arguments give related results *)
    destruct (RV_apply (k - j_1 - j_2 - 1) H_RD H_V_f H_V_2 ltac:(lia) ltac:(lia))
      as [x0 [b [b' [T1v [T1v' [Heq [Heq' HRC0]]]]]]].
    inversion Heq; subst; clear Heq.

    run_RC HRC0
      r' j'_3 Hev__r' H_V_0...

    assert (H : k - (j_1 + j_2 + 1 + j_3) = k - j_1 - j_2 - 1 - j_3)...
    rewrite H; clear H.


    match goal with | |- exists _ _, eval ?t _ _ /\ _ => destruct (dec_fully_applied t) end.
    + (* fully_applied *)
      eexists. eexists.
      split...
      eapply E_Builtin_partial...
      apply fully_applied__arg_value in f .
      eval_deterministic.
      subst.
      eassumption.
    + (* ~ fully_applied *)
      eexists. eexists.
      eauto using E_Apply, value__is_error, R_V_value_2.

  - (* E_Builtin_Apply *)

    use_approx IH_LR1 k
      H_C_e1.
    remember (close γ (msyn1 ρ) e1) as c_e1.
    remember (close γ' (msyn2 ρ) e1') as c_e1'.

    assert (H_RG' : R_G ρ (k - (applied_args c_e1)) Γ γ γ'). {
      assert (H : k - applied_args c_e1 <= k)...
      eauto using R_G_monotone.
    }
    use_approx IH_LR2 (k - applied_args c_e1)
      H_C_e2.

    remember (close γ (msyn1 ρ) e2) as c_e2.
    remember (close γ' (msyn2 ρ) e2') as c_e2'.

    autorewrite with applied_args in *.

    destruct (dec_fully_applied <{ c_e1' ⋅ c_e2' }>).
    + (* fully_applied *)

      (* c_e1 evaluates to a value (eta expansion with partially applied builtin) *)
      assert (H_FA := H1).
      apply fully_applied__Apply in H1 as [x [T [s [Hev Heq]]]].
      apply fully_applied__Apply in f as [x' [T' [s' [Hev' Heq']]]].
      run_RC H_C_e1
        r1' j_1' H_ev__e1' H_V_f...
      RV_no_error H_V_f H_V_f.
      assert (value c_e2) by admit.
      assert (value c_e2') by admit.
      apply R_C_values_to_R_V in H_C_e2 as H_V_e2...

      (* Related arguments to related results *)
      destruct (RV_apply (k - applied_args c_e1 - 1) H_RD H_V_f H_V_e2 ltac:(lia) ltac:(lia))
        as [x0 [b [b' [T1v [T1v' [Heq'' [Heq''' HRC0]]]]]]].
      inversion Heq''.
      subst x0 s r1'.
      assert (Heq_res : <{ λ x' :: T', s' }> = <{ λ x :: T1v', b' }>). {
        eauto using eval__deterministic_result.
      }
      inversion Heq_res.
      subst x s' T'.
      rewrite Heq' in HRC0.
      rewrite Heq in HRC0.

      clear - HRC0 Hev__app.

      run_RC HRC0
        r' j' H_eval' H_res'...

      all: admit.
    + (* ~fully_applied *)
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


  - (* E_Error_Apply1 *)
    rename j1 into j_1.

    assert (HRC1 :
      R_C k (Ty_Fun T1 T2) ρ (close γ (msyn1 ρ) e1) (close γ' (msyn2 ρ) e1')
    )...
Admitted.
