
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From PlutusCert Require Import 
    Normalization.BigStep
    Normalization.Normalizer_sound_complete
    Normalization.Normalizer
    PlutusIR 
    Static.Typing.Typing
    Util.List
    Equality
    Kinding.Checker
    Util
    SubstituteTCA
    UniqueTypes
    Typing.Binders_Wellkinded
    BaseKindedness.
Require Import PlutusCert.PlutusIR.Analysis.BoundVars.

From Coq Require Import Program.Equality.

(* Procedure that checks for no duplicate keys *)
Fixpoint no_dup_fun (xs : list string) := 
  match xs with
  | nil => true
  | (x::xs) => if in_dec string_dec x xs then false else no_dup_fun xs
  end.

(* Helper that returns if the kind is * *)
Definition is_KindBase (k : option kind) : bool :=
  match k with 
  | Some Kind_Base => true
  | _ => false
  end.

(* Procedure for well-formed constructures *)
Definition constructor_well_formed_check (Δ : list (binderTyname * kind)) (v : vdecl) (Tr : ty ) : bool :=
  match v with
  | VarDecl x T => let (targs, tr') := splitTy T in
          Ty_eqb Tr tr' && forallb (fun U => is_KindBase (kind_check Δ U)) targs
  end.

(* Procedure for determining whether a binding is well-formed. *)
(* Pass the recursively called type_check function as an argument even though it is not defined yet.
*)
Definition binding_well_formed_check 
  (type_check' : ((list (binderTyname * kind)) -> (list (binderName * ty)) -> term -> option ty)) 
  (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (rec : recursivity) binding : bool :=
    match binding with
    | (TypeBind (TyVarDecl X K) T) => match kind_check Δ T with
                                      | Some K' => Kind_eqb K K' (* is this K the same as in the pattern match to the left? it should be*)
                                      | _ => false
                                      end
    | (TermBind s (VarDecl x T) t) => match kind_check Δ T with
                                      | Some Kind_Base => 
                                        match type_check' Δ Γ t with   
                                        | Some Tn => match normalizer Δ T with
                                                    | Some Tn' => Ty_eqb Tn Tn'
                                                    | _ => false
                                                    end
                                        | _ => false
                                        end
                                      | _ => false
                                      end
    | (DatatypeBind (Datatype XK YKs matchFunc cs)) => 
      let dtd := Datatype XK YKs matchFunc cs in
      let X := tvdecl_name XK in
      let Ys := map tvdecl_name YKs in
      if no_dup_fun (X :: Ys) && no_dup_fun (map vdecl_name cs) then
        let Δ_ns := match rec with
                    | NonRec => drop_Δ' Δ [X]
                    | Rec => Δ
                    end in
        let Δ' := rev (map fromDecl YKs) ++ Δ_ns in
        let Tres := constrLastTyExpected dtd in
        if forallb (fun c => constructor_well_formed_check Δ' c Tres) cs then
          match rec with
            | NonRec => match kind_check (fromDecl XK :: Δ') Tres with
                        | Some Kind_Base => true 
                        | _ => false
                        end
            | Rec =>    match kind_check Δ' Tres with
                        | Some Kind_Base => true 
                        | _ => false  
                        end
          end
        else false
      else false
    end.

(* Procedure for checking well-formedness of non-recursive lists of bindings *)
(* first argument represents binding_well_formed with the type_check function already passed in *)
Definition bindings_well_formed_nonrec_check : 
  ((list (binderTyname * kind)) -> (list (binderName * ty)) -> recursivity -> binding -> bool) ->
  list (binderTyname * kind) -> (list (binderName * ty)) -> (list binding) -> bool :=
  fun b_wf =>
  fix f Δ Γ bs :=
    match bs with
      | (b::bs') =>
            match (map_normalizer (insert_deltas_rec (binds_Gamma b) (binds_Delta b ++ Δ))) with
            | Some bsGn =>
              b_wf Δ Γ NonRec b && f ((binds_Delta b) ++ Δ) (bsGn ++ Γ) bs'
            | _ => false
            end
      | _ => true
    end.

(* Procedure for checking well-formedness of recursive lists of bindings *)
Definition bindings_well_formed_rec_check : (binding -> bool) -> list binding -> bool :=
  fun b_wf =>
  fix f bs :=
    match bs with
      | (b::bs') => b_wf b && f bs'
      | _ => true
    end.

(* Procedure for checking the type of a term. *)
(* Uses normalization and kind_check procedures *)
Fixpoint type_check (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (term : term) {struct term} : (option ty) :=
    match term with
    | Var x => lookup x Γ >>= fun T => 
                match kind_check Δ T with
                | Some Kind_Base => normalizer Δ T
                | _ => None
                end
    | LamAbs x T1 t => 
        normalizer Δ T1 >>= fun T1n =>
        match type_check Δ ((x, T1n) :: Γ) t, kind_check Δ T1 with
        | Some T2, Some Kind_Base => Some (Ty_Fun T1n T2) 
        | _, _ => None
        end
    | Apply t1 t2 => 
        match type_check Δ Γ t1, type_check Δ Γ t2 with
        | Some (Ty_Fun T1 T2), Some T1' =>
            if Ty_eqb T1 T1' then Some T2 else None
        | _, _ => None
        end
    | TyAbs X K t => 
        match type_check ((X, K) :: Δ) (drop_ty_var X Γ) t with
        | Some T => Some (Ty_Forall X K T)
        | _ => None
        end
    | TyInst t1 T2 => 
        match type_check Δ Γ t1, kind_check Δ T2 with
        | Some (Ty_Forall X K2 T1), Some K2' =>
            if Kind_eqb K2 K2' then 
                normalizer Δ T2 >>= fun T2n =>
                normalizer Δ (substituteTCA X T2n T1) >>= fun T0n =>
                Some T0n
            else None
        | _, _ => None
        end
    | IWrap F T M =>
        match kind_check Δ T, kind_check Δ F, type_check Δ Γ M with
        | Some K, Some (Kind_Arrow (Kind_Arrow K' Kind_Base) (Kind_Arrow K'' Kind_Base)), Some T0n
            => if andb (Kind_eqb K K') (Kind_eqb K K'') then
                    normalizer Δ T >>= fun Tn =>
                    normalizer Δ F >>= fun Fn =>
                    normalizer Δ (unwrapIFix Fn K Tn) >>= fun T0n' =>
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
                          normalizer Δ (unwrapIFix F K T) >>= fun T0n => Some T0n
                        
                    | _  => None
                    end 
            | _ => None
            end
    | Constant (ValueOf T a) => Some (Ty_Builtin T)
    | Builtin f =>
        let T := lookupBuiltinTy f in
        normalizer Δ T >>= fun Tn =>
        Some Tn
    | Error S' => normalizer Δ S' >>= fun S'n => match kind_check Δ S' with
        | Some Kind_Base => Some S'n
        | _ => None
        end
    | Let NonRec bs t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        let xs := (insert_deltas_bind_Gamma_nr bs Δ) in
          map_normalizer xs >>= fun bsgn => 
          let Γ' := bsgn ++ Γ in
          if (bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs) then 
            type_check Δ' Γ' t >>= fun T =>
              let Δ_no_esc := drop_Δ Δ bs in
              match kind_check Δ_no_esc T with
              | Some Kind_Base => Some T
              | _ => None
              end
          else None
    | Let Rec bs t => 
        if no_dup_fun (btvbs bs) && no_dup_fun (bvbs bs) then
          let Δ' := flatten (map binds_Delta bs) ++ Δ in
          let xs := (insert_deltas_rec (flatten (map binds_Gamma bs)) Δ') in
            map_normalizer xs >>= fun bsgn =>
            let Γ' := bsgn ++ Γ in
              if (bindings_well_formed_rec_check (binding_well_formed_check type_check Δ' Γ' Rec) bs) then 
                type_check Δ' Γ' t >>= fun T =>
                  let Δ_no_esc := drop_Δ Δ bs in
                  match kind_check Δ_no_esc T with
                  | Some Kind_Base => Some T
                  | _ => None
                    end 
              else None
          else None
    | _ => None (* TODO: Case and Constr. Also not defined in the relation yet. *)
    end.
