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

Fixpoint type_check (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (term : term) : (option ty) :=
    match term with
    | Var x => lookup x Γ >>= fun T => normaliser_Jacco T
    | LamAbs x T1 t => 
        normaliser_Jacco T1 >>= fun T1n =>
        match type_check Δ ((x, T1n) :: Γ) t with
        | Some T2 => Some (Ty_Fun T1n T2) (* TODO: no normalisation of T2? Is it always normal? In the has_type efinition it is called T2n, so maybe it is*)
        | _ => None
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
