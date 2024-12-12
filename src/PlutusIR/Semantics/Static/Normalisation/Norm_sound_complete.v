From PlutusCert Require Import 
  PlutusIR 
  Normalisation.Normalisation 
  Strong_normalisation 
  Kinding.Kinding 
  Kinding.Checker
  Type_reduction
  Static.Util.
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
Qed.

(* Wouter's suggestion: do not use explicit normalizer in soundness proof*)
Theorem SN__normalise t :
  SN t -> {t' & normalise t t'}.
Proof.
  intros HSN.
  induction HSN as [t].
  (* Suppose step_d_f t = None, then t normal, then t' = t and normalise t t *)
  assert ({t' & step t t'}) as [t' Ht_steps] by admit.
  specialize (H t' Ht_steps) as [tn normt'].
  exists tn.
  now apply normalise_extend with (T2 := t').
Admitted.

Definition normaliser {T Δ K} (Hwk : Δ |-* T : K) :=
  let snt := strong_normalisation Hwk in
  projT1 (SN__normalise T snt).

Definition normaliser_Jacco T : option ty :=
  match kind_check [] T as o_kind
        return (kind_check [] T = o_kind -> option ty)
  with
  | Some K => fun Hkc =>
      Some (normaliser (kind_checking_sound [] T K Hkc))
  | None => fun _ => None
  end eq_refl.

Fixpoint map_normaliser (xs : list (string * ty)) :=
  match xs with
  | nil => Some nil
  | ((X, T) :: xs') => normaliser_Jacco T >>= fun Tn => 
                     map_normaliser xs' >>= fun xs'' =>
                     Some ((X, Tn) ::xs'')
  end.

Lemma map_normaliser_sound xs xs' :
  map_normaliser xs = Some xs' -> map_normalise xs xs'.
Proof.
Admitted.

Lemma map_normaliser_complete xs xs' :
  map_normalise xs xs' -> map_normaliser xs = Some xs'.
Proof.
Admitted.

(* Definition normaliser_Jacco T : option ty :=
  match (kind_check [] T) as placeholder 
    return ((kind_check [] T = placeholder) -> option ty) 
    with
  | Some K => fun Hkc0 => 
    let Hkc := eq_ind_r (fun o => kind_check [] T = o) eq_refl Hkc0 in
    Some (normaliser (kind_checking_sound [] T K Hkc))
  | None => fun _ => None
  end eq_refl. *)



Theorem norm_sound  Tn {T Δ K} (Hwk : Δ |-* T : K) :
  normaliser Hwk = Tn -> normalise T Tn.
Proof.
  intros.
  unfold normaliser in H.
  destruct SN__normalise in H.
  subst.
  assumption.
Qed.

Theorem norm_complete Δ K (T Tn : ty) (Hwk : Δ |-* T : K):
  normalise T Tn -> normaliser Hwk = Tn.
Proof.
  intros HnormR.
  unfold normaliser.
  destruct SN__normalise.
  simpl.
  now apply (normalisation__deterministic T x Tn) in n.
Qed.


Theorem normaliser_Jacco_sound T Tn :
  normaliser_Jacco T = Some Tn -> normalise T Tn.
Proof.
  intros Hnorm.
  unfold normaliser_Jacco in Hnorm.
  case_eq (kind_check [] T).
  - intros K Hkc.
    (* rewrite Hkc in Hnorm. abstracting over term leads to ill typed term *)
Admitted.

Theorem normaliser_Jacco_complete T Tn :
  normalise T Tn -> normaliser_Jacco T = Some Tn.
Admitted.