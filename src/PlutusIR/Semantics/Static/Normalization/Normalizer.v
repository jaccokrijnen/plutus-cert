From PlutusCert Require Import 
  PlutusIR 
  Normalization.BigStep
  Kinding.Kinding
  Kinding.Checker
  Normalization.SmallStep
  Util
  SubstituteTCA
  SN_PIR
  SN_STLC_GU
  Progress
  Normalization.Preservation.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

(* Adding a step in front does not change normal form*)
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

Definition SN := @sn ty SmallStep.step.

(* Strong normalization implies existence of normal form *)
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

(* A gas powered normalizer that does not use the strong normalization result*)
Fixpoint normalizer_gas (n : nat) {T Δ K} (Hwk : Δ |-* T : K) :=
  match n with
    | O => T
    | S n' => 
        match step_dec T Δ K Hwk with
        | inl (existT _ T' P) => 
            let Hwk' := @step_preserves_kinding T T' Δ K Hwk P in
            normalizer_gas n' Hwk'
        | inr _ => T
        end
  end.

(* Return for any well-typed input a normal form *)
Definition normalizer_wk {T Δ K} (Hwk : Δ |-* T : K) : ty :=
  let HSN := strong_normalization_PIR T Δ K Hwk in
  projT1 (SN_normalise T Δ K Hwk HSN).

(* The normalizer procedure *)
Definition normalizer Δ T : option ty :=
  match kind_check Δ T with
  | Some K => fun Hkc =>
      Some (normalizer_wk (kind_checking_sound Δ T K Hkc))
  | None => fun _ => None
  end eq_refl.

(* The normalizer only returns a normal form for well-kinded types *)
Theorem normalizer__well_kinded Δ T Tn :
  normalizer Δ T = Some Tn -> {K & Δ |-* T : K}.
Proof.
  unfold normalizer.
  move: eq_refl.
  case: {2 3}(kind_check Δ T) => // a e H.
  inversion H.
  intros.
  exists a.
  now apply kind_checking_sound.
Qed.

(* Normalise multiple types in a list.
  Each element in the list is a tuple (X, T Δ) where X is a name, T a type, and Δ the context for which we normalise T.
*)
Fixpoint map_normalizer (xs : list (string * ty * (list (string * kind)))) :=
  match xs with
  | nil => Some nil
  | ((X, T, Δ) :: xs') => normalizer Δ T >>= fun Tn => 
                     map_normalizer xs' >>= fun xs'' =>
                     Some ((X, Tn) ::xs'')
  end.

(* If a list map_normalises, then the first element also normalises *)
Lemma map_normalizer_unfold {Δ : list (string * kind)} {X T} {xs xs'} :
  map_normalizer ((X, T, Δ) :: xs) = Some xs'
  -> exists Tn xs'', (xs' = (X, Tn)::xs'') /\ normalizer Δ T = Some Tn /\ (map_normalizer xs = Some xs'').
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

(* normalizer__well_kinded for multiple types *)
Lemma map_normalizer__well_kinded xs xs' :
  map_normalizer xs = Some xs' -> map_wk xs.
Proof.
  intros.
  generalize dependent xs'.
  induction xs; intros.
  - inversion H; subst.
    constructor.
  - destruct a as [[X T] Δ].
    apply map_normalizer_unfold in H.
    destruct H as [Tn [xs'' [Heq [Hnorm Hmap]] ] ].
    apply normalizer__well_kinded in Hnorm as [K Hwk].
    apply MW_cons with (K := K).
    + apply (IHxs xs''); auto.
    + assumption.
Qed.
