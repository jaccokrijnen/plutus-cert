Require Import PlutusCert.PlutusIR.Analysis.Equality.
Require Import PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Import PlutusCert.PlutusIR.

Require Import Coq.Bool.Bool.
Require Import PlutusCert.Util.List.

Fixpoint kind_check_default_uni (d : DefaultUni) : option kind :=
  match d with
  | DefaultUniInteger 
  | DefaultUniByteString 
  | DefaultUniString 
  | DefaultUniUnit 
  | DefaultUniBool 
  | DefaultUniData 
  | DefaultUniBLS12_381_G1_Element 
  | DefaultUniBLS12_381_G2_Element 
  | DefaultUniBLS12_381_MlResult => Some Kind_Base
  | DefaultUniApply t t' =>
      match (kind_check_default_uni t, kind_check_default_uni t') with
      | (Some (Kind_Arrow k k'), Some k'') => if Kind_eqb k'' k then Some k' else None
      | _ => None
      end
  | DefaultUniProtoPair => Some (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base Kind_Base))
  | DefaultUniProtoList => Some (Kind_Arrow Kind_Base Kind_Base)
  end.

(* Tactic to simplify proofs containing hypotheses of the form
match x with
| A => Some alpha
| B _ _ => None
end = Some beta
to conclude x = A and Some alpha = Some beta.
*)
Ltac destruct_match :=
  match goal with
  | H : (match ?X with _ => _ end = _ ) |- _ => destruct X eqn:?; try discriminate
  end.

Lemma kind_checking_default_uni_sound : forall d k,
    kind_check_default_uni d = Some k -> |-*_uni d : k.
Proof with eauto.
  intros d k H. generalize dependent k.
  induction d; intros k H; inversion H; try constructor.
  - (* DefaultUniApply*) 
    repeat destruct_match.
    apply Kind_eqb_eq in Heqb.
    subst.
    apply K_DefaultUniApply with (k := k1_1).
    + apply IHd1.
      inversion H1.
      reflexivity.
    + apply IHd2.
      inversion H1.
      reflexivity. 
Qed.

Lemma kind_checking_default_uni_complete : forall d k,
    |-*_uni d : k -> kind_check_default_uni d = Some k.
Proof.
  intros d k H.
  induction H; simpl; try reflexivity.
  - (* DefaultUniApply *) 
    rewrite -> IHhas_kind_uni1.
    rewrite -> IHhas_kind_uni2.
    rewrite -> Kind_eqb_refl.
    reflexivity.
Qed.

Fixpoint kind_check (Delta : list (binderTyname * kind)) (ty : ty) : (option kind) :=
    match ty with
    | Ty_Var X => 
        lookup X Delta
    | Ty_Fun T1 T2 => 
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some Kind_Base, Some Kind_Base) => Some Kind_Base
        | (_, _) => None
        end
    | Ty_IFix F T => 
        match kind_check Delta T with
        | Some K => match kind_check Delta F with
            | Some (Kind_Arrow (Kind_Arrow K1 Kind_Base) (Kind_Arrow K2 Kind_Base)) =>
                if andb (Kind_eqb K K1) (Kind_eqb K K2) then Some Kind_Base else None
            | _ => None
            end
        | _ => None
        end
    | Ty_Forall X K T =>
        match kind_check ((X, K) :: Delta) T with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Builtin d =>
        match kind_check_default_uni d with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Lam X K1 T => 
        match kind_check ((X, K1) :: Delta) T with
        | Some K2 => Some (Kind_Arrow K1 K2)
        | _ => None
        end
    | Ty_App T1 T2 => 
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some (Kind_Arrow K11 K2), Some K12) =>
            if Kind_eqb K11 K12 then Some K2 else None
        | (_, _) => None
        end
    | Ty_SOP Tss => None  (* TODO *)
    end.

Theorem kind_checking_sound : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      apply K_Var.
      assumption.
    - (* Ty_Fun *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      apply K_Fun; 
      [apply IHty1| apply IHty2]; 
      assumption.
    - (* Ty_IFix *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      remember (kind_check Delta ty2) as K.
      apply K_IFix with (K := k). 
      + apply IHty2.
        rewrite <- HeqK.
        assumption.
      + apply IHty1.
        apply andb_true_iff in Heqb.
        destruct Heqb as [eqb1 eqb2].
        apply Kind_eqb_eq in eqb1.
        apply Kind_eqb_eq in eqb2.
        subst...
        assumption.
    - (* Ty_Forall *)
      repeat destruct_match.
      inversion H0.
      
      apply K_Forall.
      apply IHty.
      assumption.
    - (* Ty_Builtin *)
      repeat destruct_match; subst.
      inversion H0; subst.
      apply kind_checking_default_uni_sound in Heqo.
      apply K_Builtin.
      assumption.
    - (* Ty_Lam *)
      destruct_match.
      inversion H0.
      apply K_Lam. 
      apply IHty.
      assumption.
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|]; repeat destruct_match.
      apply K_App with (K1 := k1).  
        + apply IHty1.
          inversion H0.
          apply Kind_eqb_eq in Heqb.
          subst.
          assumption.
        + apply IHty2.
          rewrite HeqK1.
          reflexivity. 
Qed.

(* Identical to the above, but for Set*)
Theorem kind_checking_sound_set : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind_set Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      apply K_Var_set.
      assumption.
    - (* Ty_Fun *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      apply K_Fun_set; 
      [apply IHty1| apply IHty2]; 
      assumption.
    - (* Ty_IFix *) 
      repeat destruct_match.
      inversion H0.
      subst kind.
      remember (kind_check Delta ty2) as K.
      apply K_IFix_set with (K := k). 
      + apply IHty2.
        rewrite <- HeqK.
        assumption.
      + apply IHty1.
        apply andb_true_iff in Heqb.
        destruct Heqb as [eqb1 eqb2].
        apply Kind_eqb_eq in eqb1.
        apply Kind_eqb_eq in eqb2.
        subst...
        assumption.
    - (* Ty_Forall *)
      repeat destruct_match.
      inversion H0.
      
      apply K_Forall_set.
      apply IHty.
      assumption.
    - (* Ty_Builtin *)
      repeat destruct_match; subst.
      inversion H0; subst.
      apply kind_checking_default_uni_sound in Heqo.
      apply K_Builtin_set.
      assumption.
    - (* Ty_Lam *)
      destruct_match.
      inversion H0.
      apply K_Lam_set. 
      apply IHty.
      assumption.
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|]; repeat destruct_match.
      apply K_App_set with (K1 := k1).  
        + apply IHty1.
          inversion H0.
          apply Kind_eqb_eq in Heqb.
          subst.
          assumption.
        + apply IHty2.
          rewrite HeqK1.
          reflexivity. 
Qed.


Theorem kind_checking_complete : forall (Delta : list (binderTyname * kind)) (ty : ty) (kind : kind),
    has_kind Delta ty kind -> kind_check Delta ty = Some kind.
Proof.
    intros Delta ty kind Hkind.
    induction Hkind; simpl.
    - (* Var *)
      apply H.
    - (* Ty_Fun *)
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      reflexivity.
    - (* Ty_IFix *)
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      rewrite -> Kind_eqb_refl.
      reflexivity.
    - (* Ty_Forall *)
      rewrite IHHkind.
      auto.
    - (* Ty_Builtin *)
      apply kind_checking_default_uni_complete in H.
      rewrite -> H.
      reflexivity.
    - (* Ty_Lam *)
      rewrite IHHkind.
      auto.
    - (* Ty_App *) 
      rewrite -> IHHkind1. 
      rewrite -> IHHkind2. 
      rewrite -> Kind_eqb_refl. 
      reflexivity.
    - (* Ty_SOP: Unimplemented *)
      admit.
Admitted.

Theorem prop_to_type : forall Δ T K, has_kind Δ T K -> has_kind_set Δ T K.
Proof.
    intros Δ T K Hhk.
    apply kind_checking_complete in Hhk. (* we cannot destruct on kind_check Δ T, because then we get some arbirtary kind*)
    apply kind_checking_sound_set in Hhk.
    auto.
Qed.
