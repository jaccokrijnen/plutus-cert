
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Inductive odd : nat -> Prop := oddS : forall n:nat, even n -> odd (S n)
with even : nat -> Prop :=
  | evenO : even 0
  | evenS : forall n:nat, odd n -> even (S n).

Scheme odd_even := Minimality for odd Sort Prop
with even_odd := Minimality for even Sort Prop.

Lemma even_plus_two : forall n, even n -> even (S (S n)).
  intros.
  induction even_odd with (P := odd) (P0 := (even)) (n := n) in H; intuition.
  - apply evenS. apply oddS. apply evenO.
  - apply evenS. apply oddS. assumption.
  - apply oddS. assumption.
  - apply evenO.
  - apply evenS. assumption.
Qed.


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


(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Var x) : Tn
  | T_LamAbs : forall Δ Γ x T1 t T2n T1n,
      Δ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ ,, (x, T1n) :: Γ |-+ t : T2n ->
      Δ ,, Γ |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Δ Γ t1 t2 T1n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Fun T1n T2n) ->
      Δ ,, Γ |-+ t2 : T1n ->
      Δ ,, Γ |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Δ Γ X K t Tn,
      ((X, K) :: Δ) ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Δ Γ t1 T2 T1n X K2 T0n T2n,
      Δ ,, Γ |-+ t1 : (Ty_Forall X K2 T1n) ->
      Δ |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Δ ,, Γ |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Δ Γ F T M K Tn Fn T0n,
      Δ |-* T : K ->
      normalise T Tn ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ M : T0n ->
      Δ ,, Γ |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Δ Γ M Fn K Tn T0n,
      Δ ,, Γ |-+ M : (Ty_IFix Fn Tn) ->
      Δ |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Δ ,, Γ |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Δ Γ T a,
      Δ ,, Γ |-+ (Constant (ValueOf T a)) : (Ty_Builtin T)
  | T_Builtin : forall Δ Γ f T Tn,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Builtin f) : Tn
  | T_Error : forall Δ Γ S T Tn,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ (Error S) : Tn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Δ Γ b bs t, (* temp letrec definition for testing completeness*)
      Δ ,, Γ |-ok_b b -> (* this is more like nonrec now that we do not update Δ and Γ*)
      Δ ,, Γ |-+ (Let Rec (b :: bs) t) : Ty_Int

(* Constructors are well-formed if their result type equals the fully applied
 * datatype (the last index), and all parameter types are well-kinded
*)
with constructor_well_formed : list (string * kind) -> vdecl -> ty -> Prop :=
  | W_Con : forall Δ x T Targs Tr,
      (Targs, Tr) = splitTy T ->
      (forall U, In U Targs -> Δ |-* U : Kind_Base) ->
      Δ |-ok_c (VarDecl x T) : Tr

with bindings_well_formed_nonrec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_NonRec : forall Δ Γ,
      Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall Δ Γ b bs bsGn,
      Δ ,, Γ |-ok_b b ->
      map_normalise (binds_Gamma b) bsGn ->
      ((binds_Delta b) ++ Δ) ,, (bsGn ++ Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec : list (string * kind) -> list (string * ty) -> list binding -> Prop :=
  | W_NilB_Rec : forall Δ Γ,
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall Δ Γ b bs,
      Δ ,, Γ |-ok_b b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed : list (string * kind) -> list (string * ty) -> binding -> Prop :=
  | W_Term : forall Δ Γ s x T t Tn,
      Δ |-* T : Kind_Base ->
      normalise T Tn ->
      Δ ,, Γ |-+ t : Tn ->
      Δ ,, Γ |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall Δ Γ X K T,
      Δ |-* T : K ->
      Δ ,, Γ |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall Δ Γ X YKs cs matchFunc Δ',
      Δ' = rev (map fromDecl YKs) ++ Δ ->
      (forall c, In c cs -> Δ' |-ok_c c : (constrLastTyExpected (Datatype X YKs matchFunc cs))) ->
      Δ ,, Γ |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Δ ',,' Γ '|-+' t ':' T" := (has_type Δ Γ t T)
  and  "Δ '|-ok_c' c ':' T" := (constructor_well_formed Δ c T)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' b" := (binding_well_formed Δ Γ b).


Fixpoint allb (bs : list bool) : bool :=
    match bs with
    | [] => true
    | b::bs => andb b (allb bs)
    end.

Definition is_KindBase (k : option kind) : bool :=
  match k with 
  | Some Kind_Base => true
  | _ => false
  end.

Definition constructor_well_formed_check (Δ : list (binderTyname * kind)) (v : vdecl) (Tr : ty ) : bool :=
  match v with
  | VarDecl x T => let (targs, tr') := splitTy T in
          Ty_eqb Tr tr' && allb (map (fun U => is_KindBase (kind_check Δ U)) targs)
  end.


(* Idea Jacco: pass the recursively called type_check function as an argument even though it is not defined yet *)
Definition binding_well_formed_check 
  (type_check' : ((list (binderTyname * kind)) -> (list (binderName * ty)) -> term -> option ty)) 
  (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) binding : bool :=
    match binding with
    | (TypeBind (TyVarDecl X K) T) => match kind_check Δ T with
                                      | Some K => true (* is this K the same as in the pattern match to the left? it should be*)
                                      | _ => false
                                      end
    | (TermBind s (VarDecl x T) t) => match kind_check Δ T with
                                      | Some Kind_Base => 
                                        match type_check' Δ Γ t with   
                                        | Some Tn => match normaliser_Jacco T with
                                                    | Some Tn' => Ty_eqb Tn Tn'
                                                    | _ => false
                                                    end
                                        | _ => false
                                        end
                                      | _ => false
                                      end
    | (DatatypeBind (Datatype X YKs matchFunc cs)) => 
      let Δ' := rev (map fromDecl YKs) ++ Δ in
      allb (map (fun c => constructor_well_formed_check Δ' c (constrLastTyExpected (Datatype X YKs matchFunc cs))) cs)
    end.

(* first argument represents binding_well_formed with the type_check already passed in *)
Definition bindings_well_formed_nonrec_check : 
  ((list (binderTyname * kind)) -> (list (binderName * ty)) -> binding -> bool) ->
  list (binderTyname * kind) -> (list (binderName * ty)) -> (list binding) -> bool :=
  fun b_wf =>
  fix f Δ Γ bs :=
    match bs with
      | (b::bs') =>
            match (map_normaliser (binds_Gamma b)) with
            | Some bsGn =>
              b_wf Δ Γ b && f ((binds_Delta b) ++ Δ) (bsGn ++ Γ) bs'
            | _ => false
            end
      | [] => true
    end.

Definition bindings_well_formed_rec_check : (binding -> bool) -> list binding -> bool :=
  fun b_wf =>
  fix f bs :=
    match bs with
      | (b::bs') => b_wf b && f bs'
      | _ => true
    end.

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
    | Error S' => Some Ty_Int (* arbitrary! this will be sound but not complete *)
    | Let NonRec (b::bs) t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        map_normaliser (flatten (map binds_Gamma bs)) >>= fun bsgn =>
        let Γ' := flatten (map binds_Gamma bs) ++ Γ in
        if (bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs) then 
          type_check Δ' Γ' t >>= fun T =>
            match kind_check Δ T with
            | Some Kind_Base => Some T
            | _ => None
            end
        else None
    (* | Let Rec bs t => (* Final let rec version*)
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        map_normaliser (flatten (map binds_Gamma bs)) >>= fun bsgn =>
        let Γ' := bsgn ++ Γ in
          if (bindings_well_formed_rec_check (binding_well_formed_check type_check Δ' Γ') bs) then 
            type_check Δ' Γ' t >>= fun T =>
              match kind_check Δ T with
              | Some Kind_Base => Some T
              | _ => None
                end 
          else None *)
    | Let Rec (b::bs) t =>
        if (binding_well_formed_check type_check Δ Γ b) then Some Ty_Int else None  (* Temporarily easier efinition with only one bind check. To see how completeness works*)
         
    | _ => None
    end.

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
  - apply T_Var with (T := t)...
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
  - apply T_Error with (T := Ty_Int).
    + apply K_Builtin.
      apply K_DefaultUniInteger.
    + apply N_TyBuiltin.
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
  induction b_wf__typing__rec in H.
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
  - (* error case, not complete by implementation *) admit.
  - (* let case: later *) admit.
  - (* we dont have the necessary induction hypothesis, we need mutual recursive proof on binding_well_formed_check ? *)

Admitted.
    



      
      
      
