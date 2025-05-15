From Coq Require Extraction.

From PlutusCert Require Import 
  PlutusIR 
  Normalisation.Normalisation 
  Kinding.Kinding
  Kinding.Checker
  Type_reduction
  Static.Util
  SubstituteTCA
  port_plut2
  .
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Lemma normalise_extend T1 T2 T3 :
  step T1 T2 -> normalise T2 T3 -> normalise T1 T3.
Proof.
  intros Hstep Hnorm.
  generalize dependent T3.
  induction Hstep; intros T3 Hnorm; try solve [inversion Hnorm; try constructor; eauto].
  eapply N_BetaReduce; eauto.
  + apply N_TyLam.
    now apply normalisation__stable'__normal.
  + now apply normalisation__stable'__normal.
  + (* ADMIT: Unimplemented TY_SOP *) admit.
Admitted.

Require Import Coq.Program.Equality.

Axiom step_dec_SOP : forall l,
  normal_Ty (Ty_SOP l).

Definition step_dec (T : ty) : forall Δ K, has_kind Δ T K -> {T' & step T T'} + normal_Ty T.
Proof.
  induction T; intros.
  - right.
    repeat constructor.
  - apply kind_checking_complete in H.
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    apply kind_checking_sound in Heqo0.
    edestruct IHT1; eauto.
    + left. 
      destruct s as [t1' Ht1].
      exists (Ty_Fun t1' T2).
      now constructor.
    + edestruct IHT2; eauto.
      * left.
        destruct s as [t2' Ht2].
        exists (Ty_Fun T1 t2').
        now constructor.
  
  - apply kind_checking_complete in H.
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    apply kind_checking_sound in Heqo0.
    edestruct IHT1; eauto.
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_IFix t1' T2).
      now constructor.
    + edestruct IHT2; eauto.
      left.
      destruct s as [t2' Ht2].
      exists (Ty_IFix T1 t2').
      now constructor.
  - apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT ((b, k) :: Δ) Kind_Base Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_Forall b k t1').
      now constructor.
    + right.
      apply NO_TyForall; assumption.
  - right. apply NO_TyBuiltin. 
  - apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT ((b, k) :: Δ) k0 Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_Lam b k t1').
      now constructor.
    + right.
      apply NO_TyLam; assumption.
  - remember H as H_copy; clear HeqH_copy.
    apply kind_checking_complete in H. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
    inversion H.
    repeat destruct_match.
    apply kind_checking_sound in Heqo.
    destruct (IHT1 Δ (Kind_Arrow k0_1 k0_2) Heqo).
    + left.
      destruct s as [t1' Ht1].
      exists (Ty_App t1' T2).
      now constructor.
    + apply kind_checking_complete in H_copy. (* Note: Move to kind_checker world to fix not being able to `inversion` on `has_kind`*)
      inversion H.
      repeat destruct_match.
      apply kind_checking_sound in Heqo2.
      destruct (IHT2 Δ k2 Heqo2).
      * left.
        destruct s as [t2' Ht2].
        exists (Ty_App T1 t2').
        now constructor.
      * 
        {
        induction T1.
        - right. constructor. constructor.
          + inversion n. assumption.
          + assumption.
        - (* This does not step *)
          (* but this is also never a normal ty since Ty_Fun is never neutral*)
          exfalso.
          (* it must be ill-kinded *)
          inversion Heqo.
        - exfalso. 
          inversion Heqo.
        - exfalso.
          inversion Heqo.
        - exfalso. 
          inversion Heqo.
        - left. 
          exists (substituteTCA b T2 T1).
          constructor.
          + inversion n. assumption. inversion H0.
          + assumption.
        - right. constructor. constructor.
          + inversion n. assumption.
          + assumption.
        - apply Checker.prop_to_type in Heqo. inversion Heqo.
        }
  - right. apply step_dec_SOP. (* TODO: Different induction prniciple! *)
Defined.

Axiom step_preserves_kinding_SOP_axiom : forall l Δ,
  Δ |-* (Ty_SOP l) : Kind_Base.

(* TODO: We ended up not needing it for normalisation_preserves_kinding because we moved through normalise instead of normaliser*)
Theorem step_preserves_kinding {T T'} : forall Δ K,
  Δ |-* T : K -> step T T' -> Δ |-* T' : K.
Proof.
  intros.
  generalize dependent K.
  generalize dependent Δ.
  induction H0; intros Δ K0 Hkind_T; 
    inversion Hkind_T; subst; try solve [econstructor; eauto].
  - inversion H2; subst.
    eapply substituteTCA_preserves_kinding; eauto.
  - apply step_preserves_kinding_SOP_axiom.
Qed.

From PlutusCert Require Import SN_STLC_named_naive.

Definition SN := @sn ty Type_reduction.step.

(* Wouter's suggestion: do not use explicit normalizer in soundness proof*)
Theorem SN_normalise t Δ K :
  Δ |-* t : K -> SN t -> {t' & normalise t t'}.
Proof.
  intros HWK HSN.
  induction HSN as [t].
  destruct (step_dec t Δ K HWK).
  - destruct s0 as [t' Ht_steps].
    remember (step_preserves_kinding Δ K HWK Ht_steps) as Ht'_kind.
    specialize (H t' Ht_steps Ht'_kind) as [tn normt'].
    exists tn. now apply normalise_extend with (T2 := t').
  - exists t.
    now apply normalisation__stable'__normal.
Defined.

Fixpoint normaliser_gas (n : nat) {T Δ K} (Hwk : Δ |-* T : K) :=
  match n with
    | O => T
    | S n' => 
        match step_dec T Δ K Hwk with
        | inl (existT _ T' P) => 
            let Hwk' := @step_preserves_kinding T T' Δ K Hwk P in
            normaliser_gas n' Hwk'
        | inr _ => T
        end
  end.

Definition normaliser {T Δ K} (Hwk : Δ |-* T : K) :=
  (* normaliser_gas 100 Hwk. *)
  let HSN := plutus_ty_strong_normalization T Δ K Hwk in
  projT1 (SN_normalise T Δ K Hwk HSN).

Definition normaliser_Jacco Δ T : option ty :=
  match kind_check Δ T with
  | Some K => fun Hkc =>
      Some (normaliser (kind_checking_sound Δ T K Hkc))
  | None => fun _ => None
  end eq_refl.

Fixpoint map_normaliser (xs : list (string * ty * (list (string * kind)))) :=
  match xs with
  | nil => Some nil
  | ((X, T, Δ) :: xs') => normaliser_Jacco Δ T >>= fun Tn => 
                     map_normaliser xs' >>= fun xs'' =>
                     Some ((X, Tn) ::xs'')
  end.

Theorem norm_sound Tn {T Δ K} (Hwk : Δ |-* T : K) :
  normaliser Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normaliser in H.
  destruct SN_normalise in H.
  subst.
  assumption.
Qed.

Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normaliser Hwk = Tn.
Proof.
  intros HnormR.
  unfold normaliser.
  destruct SN_normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.

From Coq Require Import ssreflect.

Theorem normaliser_Jacco_sound Δ T Tn :
  normaliser_Jacco Δ T = Some Tn -> normalise T Tn.
Proof.
  unfold normaliser_Jacco.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TODO: I don't understand (all of) this ssreflect stuff, see https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  eapply norm_sound; eauto.
Qed.

Theorem normaliser_Jacco__well_kinded Δ T Tn :
  normaliser_Jacco Δ T = Some Tn -> {K & Δ |-* T : K}.
Proof.
  unfold normaliser_Jacco.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H. (* TODO: I don't understand (all of) this ssreflect stuff, see https://stackoverflow.com/questions/47345174/using-destruct-on-pattern-match-expression-with-convoy-pattern*)
  inversion H.
  intros.
  exists a.
  now apply kind_checking_sound.
Qed.

(* We need the well-kinded assumption, otherwise counterexample:
    nil |-* TyApp (Lam bX Kind_Base "bX") (Lam bY Kind_Base "bY")

    which normalises to Lam bY Kind_Base "bY",
    but normaliser_Jacco _ T will return None

*)
Theorem normaliser_Jacco_complete {K Δ T Tn} :
  Δ |-* T : K -> normalise T Tn -> normaliser_Jacco Δ T = Some Tn.
Proof.
  unfold normaliser_Jacco.
  intros.
  apply kind_checking_complete in H.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => //.
  - intros.
    f_equal.
    eapply norm_complete; eauto.
  - intros.
    rewrite H in e.
    discriminate.
Qed.

Lemma map_normaliser_unfold {Δ : list (string * kind)} {X T} {xs xs'} :
  map_normaliser ((X, T, Δ) :: xs) = Some xs'
  -> exists Tn xs'', (xs' = (X, Tn)::xs'') /\ normaliser_Jacco Δ T = Some Tn /\ (map_normaliser xs = Some xs'').
Proof.
  intros.
  inversion H.
  unfold bind in H1.
  repeat destruct_match.
  inversion H1.
  exists t.
  exists l.
  auto.
Qed.

Fixpoint remove_deltas  {A B C : Type} (xs : list (A * B * C)) :=
  match xs with
  | nil => nil 
  | (X, T, _) :: xs' => (X, T) :: (remove_deltas xs')
  end.

Lemma remove_deltas_app {A B C : Type} (xs ys : list (A * B * C)) :
  remove_deltas (xs ++ ys) = remove_deltas xs ++ remove_deltas ys.
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct a.
    destruct p.
    rewrite IHxs.
    reflexivity.
Qed.
    

Lemma map_normaliser_sound xs xs' :
  map_normaliser xs = Some xs' -> map_normalise (remove_deltas xs) xs'.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normaliser_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    rewrite Heq.
    constructor.
    + now apply IHxs.
    + eapply normaliser_Jacco_sound; eauto.
Qed.

Lemma map_normaliser__well_kinded xs xs' :
  map_normaliser xs = Some xs' -> map_wk xs.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normaliser_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    apply normaliser_Jacco__well_kinded in Hnorm as [K Hwk].
    apply MW_cons with (K := K).
    + apply (IHxs xs''); auto.
    + assumption.
Qed.

Require Import Coq.Program.Equality.

(* Basically we need a map_wellkinded argument *)
Lemma map_normaliser_complete {xs : list (string * ty * (list (string * kind)))} {xs'} :
  map_wk xs -> map_normalise (remove_deltas xs) xs' -> map_normaliser xs = Some xs'.
Proof.
  intros.
  dependent induction H0.
  - simpl.
    assert (xs = []). {
      unfold remove_deltas in x.
      destruct xs; auto.
      fold (@remove_deltas string) in x.
      destruct p as [p0 pff].
      destruct p0 as [X T].
      inversion x.
    }
    subst.
    reflexivity.
  - simpl.
    unfold bind.
    
    inversion H.
    + subst.
      simpl in x.
      inversion x.
    + assert (T = T0). 
      {
        unfold remove_deltas in x.
        destruct xs; [inversion H4 |].
        fold (@remove_deltas string) in x. 
        destruct p as [p0 pff].
        destruct p0 as [X1 T1].
        inversion x.
        subst.
        inversion H4.
        subst.
        reflexivity.
      }
      subst.
      apply (normaliser_Jacco_complete H3) in H1.
      specialize (IHmap_normalise xs0 H2).
      assert (Ts = remove_deltas xs0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        auto.
      }
      specialize (IHmap_normalise H4).
      unfold map_normaliser.
      rewrite H1.
      simpl.
      fold map_normaliser.
      rewrite IHmap_normalise.
      simpl.
      assert (X = X0).
      {
        unfold remove_deltas in x; fold (@remove_deltas string) in x.
        inversion x.
        subst.
        reflexivity.
      }
      subst.
      reflexivity.
Qed.

Theorem normalisation_preserves_kinding {Δ T Tn K } :
  Δ |-* T : K -> normalise T Tn -> Δ |-* Tn : K.
Proof.
  intros.
  generalize dependent K.
  generalize dependent Δ.
  induction H0; intros Δ K0 Hkind; inversion Hkind; subst; try solve [econstructor; eauto].
  - eapply IHnormalise3; eauto.
    eapply substituteTCA_preserves_kinding; eauto.
    specialize (IHnormalise1 Δ (Kind_Arrow K1 K0) H2).
    inversion IHnormalise1; subst.
    assumption.
  - (* ADMIT: Unimplemented Ty_SOP*)
    admit.
Admitted.

Theorem normaliser_preserves_kinding {Δ T Tn K } :
  Δ |-* T : K -> normaliser_Jacco Δ T = Some Tn -> Δ |-* Tn : K.
Proof.
  intros.
  apply (normaliser_Jacco_sound) in H0.
  apply (normalisation_preserves_kinding H) in H0; auto.
Qed.