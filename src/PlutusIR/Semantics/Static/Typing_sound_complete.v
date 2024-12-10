From PlutusCert Require Import 
    Normalisation.Normalisation 
    Strong_normalisation
    Norm_sound_complete
    Static.Typing 
    PlutusIR 
    Util.List
    Static.Util
    Equality
    Kinding.Checker.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Fixpoint type_check (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (term : term) : (option ty) :=
    match term with
    | Var x => lookup x Γ >>= fun T => normaliser_Jacco T
    | LamAbs x T1 t => 
        normaliser_Jacco T1 >>= fun T1n =>
        match type_check Δ ((x, T1n) :: Γ) t, kind_check Δ T1 with
        | Some T2, Some Kind_Base => Some (Ty_Fun T1n T2) (* TODO: no normalisation of T2? Is it always normal? In the has_type efinition it is called T2n, so maybe it is*)
        | _, _ => None
        end
    | Apply t1 t2 => (* TODO: normalisation? *)
        match type_check Δ Γ t1, type_check Δ Γ t2 with
        | Some (Ty_Fun T1 T2), Some T1' =>
            if Ty_eqb T1 T1' then Some T2 else None
        | _, _ => None
        end
    | TyAbs X K t => (* TODO: normalisation T?*)
        match type_check ((X, K) :: Δ) Γ t with
        | Some T => Some (Ty_Forall X K T)
        | _ => None
        end
    | TyInst t1 T2 => (* TODO: normalisation T1?*)
        match type_check Δ Γ t1, kind_check Δ T2 with (* TODO: first we check that it kind and type checks here, and then normaliser_Jacco does it again. Feels a little off*)
        | Some (Ty_Forall X K2 T1), Some K2' =>
            if Kind_eqb K2 K2' then 
                normaliser_Jacco T2 >>= fun T2n =>
                normaliser_Jacco (substituteTCA X T2n T1) >>= fun T0n =>
                Some T0n
            else None
        | _, _ => None
        end
    | IWrap F T M =>
        match kind_check Δ T, kind_check Δ F, type_check Δ Γ M with
        | Some K, Some (Kind_Arrow (Kind_Arrow K' Kind_Base) (Kind_Arrow K'' Kind_Base)), Some T0n
            => if andb (Kind_eqb K K') (Kind_eqb K K'') then
                    normaliser_Jacco T >>= fun Tn =>
                    normaliser_Jacco F >>= fun Fn =>
                    normaliser_Jacco (unwrapIFix Fn K Tn) >>= fun T0n' =>
                    if Ty_eqb T0n T0n' then 
                        Some (Ty_IFix Fn Tn)
                    else None 
                else None 
        | _, _, _ => None
        end
    | Unwrap M =>
        match type_check Δ Γ M with
            | Some (Ty_IFix F T) =>
                match kind_check Δ T with
                    | Some K =>
                        normaliser_Jacco (unwrapIFix F K T) >>= fun T0n =>
                        Some T0n
                    | _ => None
                    end 
            | _ => None
            end
    | Constant (ValueOf T a) => Some (Ty_Builtin T)
    | Builtin f =>
        let T := lookupBuiltinTy f in
        normaliser_Jacco T >>= fun Tn =>
        Some Tn
    | Error S' =>
        None (* TODO*)
    | Let NonRec bs t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        let Γ' := flatten (map binds_Gamma bs) ++ Γ in
        (* todo map_normalise function over map binds_Gamma bs*)
        (* todo bindings_well_formed_nonrec*)
        match type_check Δ' Γ' t with
            | Some T =>
                match kind_check Δ T with
                | Some Kind_Base => Some T
                | _ => None
                end 
            | _ => None
            end
    | Let Rec bs t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        let Γ' := flatten (map binds_Gamma bs) ++ Γ in
        (* todo map_normalise function over map binds_Gamma bs*)
        (* todo bindings_well_formed_rec*)
        match type_check Δ' Γ' t with
            | Some T =>
                match kind_check Δ T with
                | Some Kind_Base => Some T
                | _ => None
                end 
            | _ => None
            end 
    | _ => None
    end. (* TODO: normalisation? *)

Theorem type_checking_sound : forall Δ Γ t ty,
  type_check Δ Γ t = Some ty -> (Δ ,, Γ |-+ t : ty).
Proof with (try apply kind_checking_sound; try apply normaliser_Jacco_sound; auto).
  intros.
  generalize dependent Γ.
  generalize dependent Δ.
  generalize dependent ty.
  induction t; 
    intros ty Δ Γ Htc; 
    inversion Htc as [Htc']; 
    unfold bind in Htc'; 
    repeat destruct_match; 
    inversion Htc'; 
    subst.
  - (* Let, later *) admit.
  - (* Let later *) admit.
  - apply T_Var with (T:= t)...
  - apply T_TyAbs...
  - apply T_LamAbs...
  - eapply T_Apply.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
      apply Ty_eqb_eq in Heqb.
      now subst.
  - apply T_Constant.
  - apply normaliser_Jacco_sound in Heqo.
    now apply T_Builtin with (T := lookupBuiltinTy d).
  - apply Kind_eqb_eq in Heqb0.
    subst.
    apply T_TyInst with (X := b) (K2 := k0) (T1n := t2) (T2n := t3)...
  - apply Ty_eqb_eq in Heqb0.
    rewrite andb_true_iff in Heqb.
    destruct Heqb as [Heqb1 Heqb2].
    apply Kind_eqb_eq in Heqb1.
    apply Kind_eqb_eq in Heqb2.
    inversion Htc'.
    subst.
    apply T_IWrap with (K := k1_5) (T0n := t5)...
  - apply T_Unwrap with (Fn := t1_1) (Tn := t1_2) (K := k)...
Admitted.

(* Hmmm, why does this rewrite?? This helper lemma is of course temporary TODO *)
Lemma test (T2n T1n : ty) Δ Γ t x :
    type_check Δ ((x, T1n)::Γ) t = Some T2n -> match type_check Δ ((x, T1n)::Γ) t with 
                    | Some T2 => Some (Ty_Fun T1n T2) 
                    | None => None
                end = Some (Ty_Fun T1n T2n). 
Proof.
    intros. now rewrite H.
Qed.

(* this doesnt work inline...*)
Lemma oof2 X K Δ Γ t Tn :
type_check ((X, K) :: Δ) Γ t = Some Tn ->
 match type_check ((X, K) :: Δ) Γ t with
| Some T => Some (Ty_Forall X K T)
| None => None
end = Some (Ty_Forall X K Tn).
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.


Theorem type_checking_complete : forall Δ Γ t ty,
    (Δ ,, Γ |-+ t : ty) -> type_check Δ Γ t = Some ty.
Proof.
  intros.
  induction H; simpl; auto.
  - rewrite H.
    now apply normaliser_Jacco_complete. 
  - apply normaliser_Jacco_complete in H0; rewrite H0; simpl.
    apply kind_checking_complete in H; rewrite H.
    (* rewrite IHhas_type. Why does this not work?? *)
    now apply test.
  - rewrite IHhas_type1.
    rewrite IHhas_type2.
    now rewrite -> Ty_eqb_refl.
  - (* easy with a lemma like test *)
    now apply oof2.        
  - rewrite IHhas_type.
    apply kind_checking_complete in H0; rewrite H0.
    rewrite -> Kind_eqb_refl.
    apply normaliser_Jacco_complete in H1; rewrite H1; simpl.
    now apply normaliser_Jacco_complete in H2; rewrite H2; simpl.
  - apply kind_checking_complete in H; rewrite H.
    apply kind_checking_complete in H1; rewrite H1.
    rewrite IHhas_type.
    rewrite Kind_eqb_refl; simpl.
    apply normaliser_Jacco_complete in H0; rewrite H0; simpl.
    apply normaliser_Jacco_complete in H2; rewrite H2; simpl.
    apply normaliser_Jacco_complete in H3; rewrite H3; simpl.
    now rewrite Ty_eqb_refl.
  - rewrite IHhas_type.
    apply kind_checking_complete in H0; rewrite H0.
    now apply normaliser_Jacco_complete in H1; rewrite H1; simpl.
  - subst.
    now apply normaliser_Jacco_complete in H0; rewrite H0; simpl.
  - (* error case, not implemented yet *) admit.
  - (* let case: later *) admit.
  - (* let rec case: later *) admit.
Admitted.
    



      
      
      
