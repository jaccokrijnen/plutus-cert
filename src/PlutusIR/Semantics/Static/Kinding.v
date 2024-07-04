Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
Require Import Coq.Bool.Bool.

Require Export PlutusCert.PlutusIR.Semantics.Static.Context.

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
  | K_DefaultUniApply k k' t t' :
      |-*_uni t : (Kind_Arrow k k') ->
      |-*_uni t' : k ->
      |-*_uni (DefaultUniApply t t') : k'

  | K_DefaultUniProtoPair :
      |-*_uni DefaultUniProtoPair : (Kind_Arrow Kind_Base Kind_Base)

  | K_DefaultUniProtoList :
      |-*_uni DefaultUniProtoList : (Kind_Arrow Kind_Base Kind_Base)

  where "'|-*_uni' T ':' K" := (has_kind_uni T K)
.

Definition extractDefaultUni {d : DefaultUni} (t : typeIn d) : DefaultUni :=
  match t with
  | TypeIn _ => d
  end.

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
  | K_Builtin : forall Δ u,
      |-*_uni u : Kind_Base ->
      Δ |-* (Ty_Builtin (Some' (TypeIn u))) : Kind_Base
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (Ty_App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).

Fixpoint eqb_kind (K1 K2:kind) : bool :=
    match K1,K2 with
    | Kind_Base, Kind_Base => true
    | Kind_Arrow K11 K12, Kind_Arrow K21 K22 =>
        andb (eqb_kind K11 K21) (eqb_kind K12 K22)
    | _, _ => false
    end.

(* Based on Software Foundation's eqb_type_refl *)
Lemma eqb_kind_refl : forall kind,
    eqb_kind kind kind = true.
Proof.
    intros kind.
    induction kind.
    - simpl. reflexivity.
    - simpl. rewrite -> IHkind1. rewrite -> IHkind2. simpl. reflexivity.
Qed.

(* Based on Software Foundation's eqb_type_eq*)
Lemma eqb_kind_eq : forall K1 K2,
    eqb_kind K1 K2 = true -> K1 = K2.
Proof with auto.
    intros K1. induction K1; intros K2 HBeq; destruct K2; inversion HBeq.
    - reflexivity.
    - rewrite andb_true_iff in H0. 
      inversion H0 as [Hbeq1 Hbeq2].
      apply IHK1_1 in Hbeq1.
      apply IHK1_2 in Hbeq2.
      subst...
Qed.

Fixpoint kind_check (gamma : list (binderTyname * kind)) (ty : ty) : (option kind) :=
    match ty with
    | Ty_Var X => (* Based on Software Foundations and has_kind *)
        lookup X gamma
    | Ty_Fun T1 T2 => (* TODO: I don't understand what this datatype does*)
        match (kind_check gamma T1, kind_check gamma T2) with
        | (Some Kind_Base, Some Kind_base) => Some Kind_Base
        | (_, _) => None
        end
    | Ty_IFix F T => (* Note: Purely based on structure of has_kind *)
        match kind_check gamma T with
        | Some K => match kind_check gamma F with
            | Some (Kind_Arrow (Kind_Arrow K1 Kind_Base) (Kind_Arrow K2 Kind_Base)) =>
                if andb (eqb_kind K K1) (eqb_kind K K2) then Some Kind_Base else None
            | _ => None
            end
        | _ => None
        end
    | Ty_Forall X K T =>
        match kind_check ((X, K) :: gamma) T with
        | Some Kind_Base => Some Kind_Base
        | _ => None
        end
    | Ty_Builtin (Some' typeIn) =>
        let d := extractDefaultUni typeIn in
        Some (lookupBuiltinKind d)
    | Ty_Lam X K1 T => (* Note: Copied from Software Foundations *)
        match kind_check ((X, K1) :: gamma) T with
        | Some K2 => Some (Kind_Arrow K1 K2)
        | _ => None
        end
    | Ty_App T1 T2 => (* TODO: Check, because: Made up myself!*)
        match (kind_check gamma T1, kind_check gamma T2) with
        | (Some (Kind_Arrow K11 K2), Some K12) =>
            if eqb_kind K11 K12 then Some K2 else None
        | (_, _) => None
        end
    end.

Theorem kind_checking_sound : forall Gamma ty kind,
    kind_check Gamma ty = Some kind -> has_kind Gamma ty kind.
Proof.
    intros Gamma ty. generalize dependent Gamma.
    induction ty; intros Gamma kind Htc; inversion Htc.
    - (* Var *) 
      destruct (lookup t Gamma) eqn:H.
      + apply K_Var with (K := kind). 
        rewrite H0 in H.
        apply H.
      + discriminate.
    - (* Ty_Fun *) shelve.
    - (* Ty_IFix *) shelve.
    - (* Ty_Forall *) shelve.
    - (* Ty_Builtin *) shelve.
    - (* Ty_Lam *) shelve.
    - (* Ty_App *) 
      (* TODO: Attempt stuck*)
      remember (kind_check Gamma ty1) as K1.
      remember (kind_check Gamma ty2) as K2.
      destruct K1 as [k1|] eqn:HK1; [ | discriminate]. (* Successfully extract k1 *)
      destruct K2 as [k2|] eqn:HK2. (* Successfully extract k2 *)
      + apply K_App with (K1 := k1).
        * shelve.
        * shelve.
      + shelve.      
(* Abort. *)


Theorem kind_checking_complete : forall (gamma : list (binderTyname * kind)) (ty : ty) (kind : kind),
    has_kind gamma ty kind -> kind_check gamma ty = Some kind.
Proof.
    intros gamma ty kind Hkind.
    induction Hkind. simpl.
    - (* Var *)
      apply H.
    - (* Ty_Fun *)
      simpl.
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      reflexivity.
    - (* Ty_IFix *)
      simpl.
      rewrite -> IHHkind1.
      rewrite -> IHHkind2.
      rewrite -> eqb_kind_refl.
      simpl.
      reflexivity.
    - (* Ty_Forall *)
      simpl.
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_Builtin *)
      simpl.
      rewrite -> H.
      reflexivity.
    - (* Ty_Lam *)
      simpl.
      rewrite -> IHHkind.
      reflexivity.
    - (* Ty_App *) 
      simpl.
      rewrite -> IHHkind1. 
      rewrite -> IHHkind2. 
      rewrite -> eqb_kind_refl. 
      reflexivity.
Abort.



(* Ltac solve_by_inverts n :=
  match goal with
  | H: ?T |- _ =>
    match type of T with
    | Prop =>
      inversion H;
      subst;
      match n with
      | 0 => idtac
      | S ?n' => solve_by_inverts n'
      end
    end
  end.
  

Ltac solve_by_invert :=
  solve_by_inverts 1. *)