Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
Require Import Coq.Bool.Bool.

Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Import PlutusCert.PlutusIR.Analysis.Equality.
Require Import List.
Import ListNotations.

Import PlutusNotations.

Reserved Notation "'|-*_uni' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind_uni : DefaultUni -> kind -> Prop :=
  | K_DefaultUniInteger :
      |-*_uni DefaultUniInteger : Kind_Base
  | K_DefaultUniByteString :
      |-*_uni DefaultUniByteString : Kind_Base
  | K_DefaultUniString :
      |-*_uni DefaultUniString : Kind_Base
  | K_DefaultUniUnit :
      |-*_uni DefaultUniUnit : Kind_Base
  | K_DefaultUniBool :
      |-*_uni DefaultUniBool : Kind_Base
  | K_DefaultUniData :
      |-*_uni DefaultUniData : Kind_Base
  | K_DefaultUniBLS12_381_G1_Element :
      |-*_uni DefaultUniBLS12_381_G1_Element : Kind_Base
  | K_DefaultUniBLS12_381_G2_Element :
      |-*_uni DefaultUniBLS12_381_G2_Element : Kind_Base
  | K_DefaultUniBLS12_381_MlResult :
      |-*_uni DefaultUniBLS12_381_MlResult : Kind_Base
  | K_DefaultUniApply : forall k k' t t',
      |-*_uni t : (Kind_Arrow k k') ->
      |-*_uni t' : k ->
      |-*_uni (DefaultUniApply t t') : k'
  | K_DefaultUniProtoPair :
      |-*_uni DefaultUniProtoPair : (Kind_Arrow Kind_Base Kind_Base)
  | K_DefaultUniProtoList :
      |-*_uni DefaultUniProtoList : (Kind_Arrow Kind_Base Kind_Base)
  where "'|-*_uni' T ':' K" := (has_kind_uni T K)
.

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
  | DefaultUniProtoPair
  | DefaultUniProtoList => Some (Kind_Arrow Kind_Base Kind_Base)
  end.

Lemma kind_checking_default_uni_sound : forall d k,
    kind_check_default_uni d = Some k -> |-*_uni d : k.
Proof with eauto.
  intros d k H. generalize dependent k.
  induction d; intros k H; inversion H; try constructor.
  - (* DefaultUniApply*) 
    destruct (kind_check_default_uni d1) eqn:Hd1; [|discriminate].
    destruct k0 eqn:Hk0; [discriminate|].
    destruct (kind_check_default_uni d2) eqn:Hd2; [|discriminate].
    destruct (Kind_eqb k1 k1_1) eqn:Heqb; [|discriminate].
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

(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : list (binderTyname * kind) -> ty -> kind -> Prop :=
  | K_Var : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-* (Ty_Var X) : K
  | K_Fun : forall Δ T1 T2,
      Δ |-* T1 : Kind_Base ->
      Δ |-* T2 : Kind_Base ->
      Δ |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall Δ F T K,
      Δ |-* T : K ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Δ |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall Δ X K T,
      ((X, K) :: Δ) |-* T : Kind_Base ->
      Δ |-* (Ty_Forall X K T) : Kind_Base
  | K_Builtin : forall Δ T K,
      |-*_uni T : K ->
      Δ |-* (Ty_Builtin T) : K
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (Ty_App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).

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
        kind_check_default_uni d
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
    end.

Theorem kind_checking_sound : forall Delta ty kind,
    kind_check Delta ty = Some kind -> has_kind Delta ty kind.
Proof.
    intros Delta ty. generalize dependent Delta.
    induction ty; intros Delta kind Htc; inversion Htc.
    - (* Var *) 
      destruct (lookup t Delta) eqn:H; [|discriminate].
      apply K_Var.
      rewrite H0 in H.
      apply H.
    - (* Ty_Fun *) 
      assert (kind = Kind_Base) as Hkind_base.
      {
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [|discriminate].
        destruct (kind_check Delta ty2); [|discriminate].
        destruct k; [|discriminate].
        inversion H0.
        reflexivity.
      }
      subst kind.
      apply K_Fun.
      + apply IHty1.
        destruct (kind_check Delta ty1) eqn:Hkc; [|discriminate].
        destruct k; [|discriminate].
        reflexivity.        
      + apply IHty2.
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [|discriminate].
        destruct (kind_check Delta ty2); [|discriminate].
        destruct k; [|discriminate].
        reflexivity.
    - (* Ty_IFix *) 
      assert (kind = Kind_Base) as Hkind_base.
      {
        (* TODO: Code duplication with after apply IHty1*)
        destruct (kind_check Delta ty2); [|discriminate].
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k0; [discriminate|].
        destruct k0_1; [discriminate|].
        destruct k0_1_2; [|discriminate].
        destruct k0_2; [discriminate|].
        destruct k0_2_2; [|discriminate].
        destruct (Kind_eqb k k0_1_1 && Kind_eqb k k0_2_1); [|discriminate].
        inversion H0.
        reflexivity.
      }
      subst kind.
      remember (kind_check Delta ty2) as K.
      destruct K as [k|]; [|discriminate].
      apply K_IFix with (K := k). 
      + apply IHty2.
        rewrite HeqK.
        reflexivity. 
      + apply IHty1.
        destruct (kind_check Delta ty1); [|discriminate].
        destruct k0; [discriminate|].
        destruct k0_1; [discriminate|].
        destruct k0_1_2; [|discriminate].
        destruct k0_2; [discriminate|].
        destruct k0_2_2; [|discriminate].
        destruct (Kind_eqb k k0_1_1 && Kind_eqb k k0_2_1) eqn:eqbs; [|discriminate].
        apply andb_true_iff in eqbs.
        destruct eqbs as [eqb1 eqb2].
        apply Kind_eqb_eq in eqb1.
        apply Kind_eqb_eq in eqb2.
        subst...
        reflexivity.
    - (* Ty_Forall *)
      assert (kind = Kind_Base) as Hkind_base.
      {
        destruct (kind_check ((b, k) :: Delta) ty); [|discriminate].
        destruct k0; [|discriminate].
        inversion H0.
        reflexivity.
      }
      rewrite Hkind_base. 
      (* The result of the K_Forall case matches and thus we can apply it!*)
      apply K_Forall.
      (* Now this is in the form of our induction hypothesis*)
      apply IHty.
      (* Final steps, use H0, which derives from the definition of kind_check*)
      destruct (kind_check ((b, k) :: Delta) ty) as [k0|]; [|discriminate].
      destruct k0; [|discriminate];
      rewrite -> H0.
      reflexivity.
    - (* Ty_Builtin *)
      apply kind_checking_default_uni_sound in H0.
      apply K_Builtin.
      assumption.
    - (* Ty_Lam *)
      destruct (kind_check ((b, k) :: Delta) ty) eqn:Hkc; [|discriminate].
      inversion H0.
      apply K_Lam. (* Apply has_kind structure*)
      apply IHty.
      apply Hkc. (* Apply kind_check structure*)
    - (* Ty_App *) 
      remember (kind_check Delta ty2) as K1.
      destruct K1 as [k1|].
      + apply K_App with (K1 := k1).  
        * apply IHty1.
          destruct (kind_check Delta ty1); [|discriminate].
          destruct k; [discriminate|].
          destruct (Kind_eqb k2 k1) eqn:eqb ; [|discriminate].
          inversion H0.
          apply Kind_eqb_eq in eqb.
          rewrite eqb.
          reflexivity.
        * apply IHty2.
          rewrite HeqK1.
          reflexivity. 
      + destruct (kind_check Delta ty1); [|discriminate].
        destruct k; [discriminate|discriminate].
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
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_Builtin *)
      apply kind_checking_default_uni_complete in H.
      assumption.
    - (* Ty_Lam *)
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_App *) 
      rewrite -> IHHkind1. 
      rewrite -> IHHkind2. 
      rewrite -> Kind_eqb_refl. 
      reflexivity.
Qed.