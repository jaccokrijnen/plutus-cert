From PlutusCert Require Import STLC_named STLC_normalisation SN_STLC_named STLC_named_typing util.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.

(* Used to do induction over the size of SN proofs *)
Fixpoint mysn_size {t : term} (HSN : MySN t) : nat :=
  match HSN with
  | SNI0 _ => 0
  | SNI' (existT _ t' (_, HSN')) => 1 + mysn_size HSN'
  end.

Lemma mysn_size_helper {t : term} (HSN : MySN t) :
  forall f, @mysn_size t (SNI' f) <> 0.
Proof.
  intros f.
  simpl.
  destruct f as [t' p].
  destruct p as [_ HSN'].
  intros Hcontra.
  inversion Hcontra.
Qed.

Lemma norm_lam tb x T (snt : (MySN (tmlam x T tb))) (sntb : MySN tb):
  @normalizer' (tmlam x T tb) snt = tmlam x T (@normalizer' tb sntb).
Proof.
  intros.
  remember (mysn_size snt) as n.
  generalize dependent tb.
  induction n.
  - intros tb snt sntb Hsize.
    remember snt as snt_copy.
    clear Heqsnt_copy.
    destruct snt_copy.
    + (* no step for the outer lambda, so we should also get: no step for the inner lambda *)
      induction sntb.
      * simpl.
        reflexivity.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        clear Hsize.
        inversion e.
        unfold bind in H0.
        assert (step_d_f tb = None) by destruct_match.

        rewrite Hstept' in H.
        inversion H.
    + exfalso.
      inversion Hsize.
      simpl in H0.
      destruct H0.
      assert (mysn_size (SNI' (t := tmlam x T tb) s) <> 0).
      {
        apply mysn_size_helper.
        assumption.
      }
      rewrite <- Hsize in H.
      contradiction.    
  - induction sntb.
    + intros Hsize.
      induction snt.
      * simpl. reflexivity.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        clear Hsize.
        inversion Hstept'.
        unfold bind in H0.
        assert (step_d_f tb <> None) by destruct_match.
        (* contradiction: body does not step, while lambda does *)
        contradiction.
    + destruct snt.
      * exfalso.
        destruct s as [t' [Hstept' HSNt'] ].
        inversion e.
        unfold bind in H0.
        destruct_match.
      * (* size not 0 and both step: the interesting case *) 
        
        destruct s as [tb' [Hsteptb' HSNtb'] ].
        destruct s0 as [t' [Hstept' HSNt'] ].

        simpl.
        assert (tmlam x T tb' = t').
        {
          inversion Hstept'.
          unfold bind in H0.
          destruct_match.
          inversion H0.
          inversion Hsteptb'.
          reflexivity.
        }
        subst.
        simpl.
        specialize IHn with (tb := tb') (snt := HSNt') (sntb := HSNtb').
        intros.
        inversion Heqn.
        specialize (IHn H0).
        assumption.
Qed.

(* TODO: DCopied from SubstitutionPreservesTyping/substitueTca
  In that file it is defined for PlutusIR and proof is started.
 *)
Theorem substituteTCA_preserves_kinding : forall T Delta X K U L,
    SN_STLC_named.has_type ((X, L) :: Delta) T K ->
    SN_STLC_named.has_type Delta U L ->
    SN_STLC_named.has_type Delta (substituteTCA X U T) K.
Admitted.

(* Needs a neutrality requirement *)
Lemma norm_app t1 t2 (snt : (MySN (tmapp t1 t2))) (snt1 : MySN t1) (snt2 : MySN t2) :
  STLC_normalisation.neutral_Ty (@normalizer' t1 snt1) -> @normalizer' (tmapp t1 t2) snt = tmapp (@normalizer' t1 snt1) (@normalizer' t2 snt2).
Admitted.

(* Looks complicated, but it is really a step forward, since there is no mention of normalise anymore
  If it is too difficult, we can first try to do it with t1 already normalized fully I think.
*)
Lemma norm_subst t1 t2 T1n bX K1 (snt : (MySN (tmapp t1 t2))) (snt1 : (MySN t1)) (snt2 : (MySN t2)) 
    (snsub : (MySN (substituteTCA bX (@normalizer' t2 snt2) T1n))) :
  @normalizer' t1 snt1 = tmlam bX K1 T1n -> 
    @normalizer' (tmapp t1 t2) snt = @normalizer' (substituteTCA bX (@normalizer' t2 snt2) T1n) snsub.
Admitted.

Theorem norm_complete Δ K (t tn : term) (Hwt : SN_STLC_named.has_type Δ t K):
  normalise t tn -> @normalizer t Δ K Hwt = tn.
Proof.
  intros HnormR.
  generalize dependent Δ.
  generalize dependent K.
  induction HnormR; intros K' Δ Hwt; subst; auto.
  - inversion Hwt; subst. (* normalise T1 (tmlam bX K T1n), so T1 is a lambda as well. 
      What if it is an app before beta reduction?*)
    (* inversion HnormR1; subst. *)
    specialize (IHHnormR2 K1 Δ H4).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H2). (* we need something like step preserves type? K' = K1 I think*)

    specialize (IHHnormR3 K' Δ). (* The body of the lambda has just type K'*)

    assert (SN_STLC_named.has_type Δ (substituteTCA bX T2n T1n) K').
    {
      apply substituteTCA_preserves_kinding with (L := K1).
      - (* By normalizer preserves typing we have Δ ⊢* (tmlam bX K T1n) : K1 → K'
              Hence K = K1 and
              (bX, K1)::Δ ⊢* T1n : K'
      *) admit.
      - (* By normalizer preserves typing we have Δ ⊢* T2n : K1  . *)
        admit.
    }
    specialize (IHHnormR3 H).
    subst.
    eapply norm_subst.
    exact IHHnormR1.

  - inversion Hwt; subst.
    rewrite <- (IHHnormR2 K1 Δ H5).
    specialize (IHHnormR1 (tp_arrow K1 K') Δ H3).
    subst.
    now apply norm_app.
  - inversion Hwt; subst.
    rewrite <- (IHHnormR K2 ((bX, K)::Δ) H4).
    apply norm_lam.
  - unfold normalizer.
    destruct (strong_normalization_mysn Hwt).
    unfold normalizer'.
    reflexivity.
Admitted.

Lemma normalise_extend T1 T2 T3 :
  step_d T1 T2 -> normalise T2 T3 -> normalise T1 T3.
Proof.
  intros Hstep Hnorm.
  generalize dependent T3.
  induction Hstep; intros T3 Hnorm; try solve [inversion Hnorm; try constructor; eauto].
  - eapply N_BetaReduce; eauto.
    + apply N_TyLam.
      admit (* Follows from normalisation__stable'__normal *).
    + admit.  
Admitted.

Inductive MySN2 t : Set :=
| SNI2 : (forall t', step_d_f t = Some t' -> (MySN2 t')) -> MySN2 t. (* TODO: cannot find the inductive step, but removing the existential might work*)
(* This is the same as the exists, why??? *)

(* With MySN' t we get the necessary induciton hypothesis! *)
Theorem norm_sound'' (t tn : term) (snt : MySN t) :
  normalizer' snt = tn -> normalise t tn.
Proof.
  intros Hnorm.
  unfold normalizer in Hnorm.
  assert (sn2t: MySN2 t) by admit.
  induction sn2t.
  (* assume there is a t' s.t. step_d_f t = Some t'*)
  assert ({t' & step_d_f t = Some t'}) as [t' Hstep] by admit.
  assert (step_d t t') by admit.
  apply (normalise_extend t t' tn H0).
  eapply (H t'); eauto.
  
    (* should be sn't, but we have to change normalizer' definition first. *)
Admitted.

Inductive MySN' t : Set :=
| SNI0' : (step_d_f t = None) -> MySN' t
| SNI'' : forall t', step_d_f t = Some t' -> (MySN' t') -> MySN' t. (* TODO: cannot find the inductive step, but removing the existential might work*)
(* This is the same as the exists, why??? *)

(* With MySN' t we get the necessary induciton hypothesis! *)
Theorem norm_sound' (t tn : term) (snt : MySN t) :
  normalizer' snt = tn -> normalise t tn.
Proof.
  intros Hnorm.
  unfold normalizer in Hnorm.
  assert (sn't: MySN' t) by admit.
  induction sn't.
  - (* no step: easy *)
    admit.
  - assert (step_d t t') by admit.
    apply (normalise_extend t t' tn H).
    eapply IHsn't.
    (* should be sn't*)
Admitted.

Theorem norm_sound Δ T (t tn : term) (Hwt : SN_STLC_named.has_type Δ t T) :
    normalizer Hwt = tn -> normalise t tn.
Proof.
  intros Hnorm.
  induction Hnorm.
  
  induction Hwt.
  - unfold normalizer.
    destruct (strong_normalization_mysn).
    + simpl.
      apply N_TyVar.
    + exfalso.
      destruct s as [t' [Hstep HSN] ].
      inversion Hstep.
  - unfold normalizer.
    destruct (strong_normalization_mysn).
    + simpl.
      apply N_TyLam.
      unfold normalizer in IHHwt.
      destruct (strong_normalization_mysn Hwt) in IHHwt.
      * simpl in IHHwt.
        assumption.
      * exfalso.
        destruct s as [t' [Hstep HSN] ].
        inversion e.
        unfold bind in H0.
        assert (step_d_f T = None).
        {
          admit. (* destruct match ???*)
        } 
        rewrite Hstep in H.
        inversion H.
    + (* lambda steps! *)
      destruct s as [t' [Hstep HSN] ].
      unfold normalizer in IHHwt.
      destruct (strong_normalization_mysn Hwt) in IHHwt.
      * exfalso.
        (* lam body no step, while whole lambda steps, contradiction*)
        admit.
      * simpl.
        destruct s as [t'0 [Hstept'0 HSNt'0] ].
        inversion Hstep.
        unfold bind in H0.
        assert (step_d_f T = Some t'0) by admit. (* destruct match *)
        assert (tmlam X K1 t'0 = t') by admit. (* destruct match *)
        subst.
        rewrite norm_lam with (sntb := HSNt'0).
        apply N_TyLam.
        simpl in IHHwt.
        assumption. 
  - unfold normalizer.
    remember (SN_STLC_named.K_App Hwt1 Hwt2) as K.
    remember (mysn_size (strong_normalization_mysn K)) as n.
    (* generalize dependent Hwt1.
    generalize dependent K. *)
    generalize dependent K2.
    dependent induction n; intros K2 Hwt1 IHHwt1 K HK Hsize.
    + admit.
    + destruct (is_neutral (normalizer Hwt1)) eqn:neut.
      * rewrite norm_app with (snt1 := strong_normalization_mysn Hwt1) (snt2 := strong_normalization_mysn Hwt2).
        apply N_TyApp.
        -- simpl in IHHwt1.
           assumption.
        -- unfold normalizer in neut.
          (* is_neutral and neutral_Ty are sound/complete*)
           admit.
        -- simpl in IHHwt2.
           assumption.
        -- unfold normalizer in neut.
            admit. (* same case as second..., generate by rewrite norm_app *)
      * (* not neutral, hence T1n is a lam! Hence we will substitute! *)
        (* We need to know the shape of T1n, what is the binder name and the kind *)

        assert ({x & {K1 & {T1n & normalizer Hwt1 = tmlam x K1 T1n}}}) as [x [ K1' [ T1n Hnormlam ] ] ] by admit.

        assert (Htypesub: SN_STLC_named.has_type Δ (substituteTCA x (normalizer Hwt2) T1n) K2).
        {
          admit.
        }

        (* rewrite norm_subst with (T1n := T1n) (bX := x) (K1 := K1')
          (snt1 := strong_normalization_mysn Hwt1) (snt2 := strong_normalization_mysn Hwt2)
          (snsub := strong_normalization_mysn (Htypesub))
          . *)

        (*

        We want to use IHn.

        We need n= mysn_size (strong_normalisation_mysn ). We can assume we have it:
        that T1 = already in normall ambda form and thus T1 = T1n.

        TODO: IHn needs to be generic over kind


        Do we have Htypesub = (SN_STLC_named.K_App Hwt1 Hwt2) ? I think so!

        I guess we could use the IH to let tmapp T1 T2 do one step to say T_one.
        Then this normalises in n steps to (normalizer K).

        Then we know T_one |-> normalizer' (strong_normalization_mysn T_one)

        But also  T_one |-> normalizer' (strong_normalization_mysn (tmapp T1 T2)).

        So we know

        normalise T_one (strong_normalization_mysn (tmapp T1 T2)).

        Then we can use normalise_extend to construct the higher normalise!

        *)
        specialize (IHn K2 Hwt1 IHHwt1 K HK). (* faulty reasoning, wen eed to do one step or something*)
        assert (T1 = tmlam x K1' T1n) by admit.
        subst.
        eapply N_BetaReduce.
        -- rewrite Hnormlam in IHHwt1.
           exact IHHwt1.
        -- exact IHHwt2.
        --
        admit.
        -- exact Hnormlam.

Admitted.
