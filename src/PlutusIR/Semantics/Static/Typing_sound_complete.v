From PlutusCert Require Import 
    Normalisation.Normalisation 
    Strong_normalisation
    Norm_sound_complete
    Static.Typing 
    PlutusIR 
    Util.List
    Static.Util.

Fixpoint type_check (Γ : list (binderName * ty)) (term : term) : (option ty) :=
    match term with
    | Var x => lookup x Γ >>= fun T => normaliser_Jacco T
    | LamAbs x T1 t => 
        normaliser_Jacco T1 >>= fun T1n =>
        match type_check ((x, T1n) :: Γ) t with
        | Some T2 => Some (Ty_Fun T1n T2) (* TODO: no normalisation of T2? Is it always normal? In the has_type efinition it is called T2n, so maybe it is*)
        | _ => None
        end
    (* | Apply t1 t2 =>
        match type_check Γ t1, type_check Γ t2 with
        | Some (Ty_Fun T1 T2), Some T1' =>
            if eqb_ty T1 T1' then Some T2 else None
        | (_, _) => None
        end *)
    | _ => None (* TODO *)
    end. (* TODO: normalisation? *)




    | Ty_Var X => (* Based on Software Foundations and has_kind *)
        lookup X Delta
    | Ty_Fun T1 T2 => (* TODO: I don't understand what this datatype does*)
        match (kind_check Delta T1, kind_check Delta T2) with
        | (Some Kind_Base, Some Kind_Base) => Some Kind_Base
        | (_, _) => None
        end
    | Ty_IFix F T => (* Note: Purely based on structure of has_kind *)
        match kind_check Delta T with
        | Some K => match kind_check Delta F with
            | Some (Kind_Arrow (Kind_Arrow K1 Kind_Base) (Kind_Arrow K2 Kind_Base)) =>
                if andb (eqb_kind K K1) (eqb_kind K K2) then Some Kind_Base else None
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
            if eqb_kind K11 K12 then Some K2 else None
        | (_, _) => None
        end
    end.


