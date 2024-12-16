
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

From PlutusCert Require Import 
    Normalisation.Normalisation 
    Strong_normalisation
    Norm_sound_complete
    Static.Typing 
    PlutusIR 
    Util.List
    Static.Util
    Equality
    Kinding.Checker
    Util.


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
  | T_LetRec : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let Rec bs t) : Tn
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

Scheme has_type_mut_ind := Induction for has_type Sort Prop
with bs_wf_mut_ind := Induction for bindings_well_formed_rec Sort Prop
with bs_wf_nonrec_mut_ind := Induction for bindings_well_formed_nonrec Sort Prop
with b_wf_mut_ind := Induction for binding_well_formed Sort Prop.

Fixpoint allbmap {A : Type} (f : A -> bool) (bs : list A) : bool :=
    match bs with
    | [] => true
    | b::bs => andb (f b) (allbmap f bs)
    end.

Lemma allb_element_true : forall A f bs b, In b bs -> @allbmap A f bs = true -> f b = true.
Proof.
  intros.
  induction bs.
  - inversion H.
  - simpl in H0.
    destruct H.
    + subst.
      simpl in H0.
      apply andb_true_iff in H0.
      destruct H0.
      assumption.
    + apply andb_true_iff in H0.
      destruct H0.
      apply IHbs; auto.
Qed.

Lemma allbmap_each : forall A f bs, (forall b, In b bs -> f b = true) -> @allbmap A f bs = true.
Proof.
  intros.
  induction bs.
  - simpl. reflexivity.
  - simpl.
    apply andb_true_iff.
    split.
    + apply H. left. reflexivity.
    + apply IHbs.
      intros.
      apply H.
      right. assumption.
Qed.

Definition is_KindBase (k : option kind) : bool :=
  match k with 
  | Some Kind_Base => true
  | _ => false
  end.

Definition constructor_well_formed_check (Δ : list (binderTyname * kind)) (v : vdecl) (Tr : ty ) : bool :=
  match v with
  | VarDecl x T => let (targs, tr') := splitTy T in
          Ty_eqb Tr tr' && allbmap (fun U => is_KindBase (kind_check Δ U)) targs
  end.


(* Idea Jacco: pass the recursively called type_check function as an argument even though it is not defined yet 
Make another version that already has type_check as argument after type_check is defined.
*)
Definition binding_well_formed_check 
  (type_check' : ((list (binderTyname * kind)) -> (list (binderName * ty)) -> term -> option ty)) 
  (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) binding : bool :=
    match binding with
    | (TypeBind (TyVarDecl X K) T) => match kind_check Δ T with
                                      | Some K' => Kind_eqb K K' (* is this K the same as in the pattern match to the left? it should be*)
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
      allbmap (fun c => constructor_well_formed_check Δ' c (constrLastTyExpected (Datatype X YKs matchFunc cs))) cs
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
      | _ => true
    end.

Definition bindings_well_formed_rec_check : (binding -> bool) -> list binding -> bool :=
  fun b_wf =>
  fix f bs :=
    match bs with
      | (b::bs') => b_wf b && f bs'
      | _ => true
    end.

Fixpoint type_check (Δ : list (binderTyname * kind)) (Γ : list (binderName * ty)) (term : term) {struct term} : (option ty) :=
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
    | Error S' => Some Ty_Int (* arbitrary! this will be sound but not complete (zie teams Jacco over preservation type errors (app case))*)
    | Let NonRec bs t =>
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        map_normaliser (flatten (map binds_Gamma bs)) >>= fun bsgn =>
        let Γ' := bsgn ++ Γ in
        if (bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs) then 
          type_check Δ' Γ' t >>= fun T =>
            match kind_check Δ T with
            | Some Kind_Base => Some T
            | _ => None
            end
        else None
    | Let Rec bs t => (* Final let rec version*)
        let Δ' := flatten (map binds_Delta bs) ++ Δ in
        map_normaliser (flatten (map binds_Gamma bs)) >>= fun bsgn =>
        let Γ' := bsgn ++ Γ in
          if (bindings_well_formed_rec_check (binding_well_formed_check type_check Δ' Γ') bs) then 
            type_check Δ' Γ' t >>= fun T =>
              match kind_check Δ T with
              | Some Kind_Base => Some T
              | _ => None
                end 
          else None
    | _ => None (* TODO: Case and Constr?? *)
    end.

Section term_recursivity_rect.
  Variable (P : term -> Type).
  Variable (Q : binding -> Type).
  Variable (R : list binding -> Type).
  Variable (S : list binding -> Type).

  Context
    (* (H_Let     : forall rec bs t, ForallT Q bs -> P t -> P (Let rec bs t)) *)
    (H_LetRec     : forall bs t, R bs -> P t -> P (Let Rec bs t))
    (H_LetNonRec  : forall bs t, S bs -> P t -> P (Let NonRec bs t))
    (H_Var     : forall s, P (Var s))
    (H_TyAbs   : forall s (k : kind) (t : term), P t -> P (TyAbs s k t))
    (H_LamAbs  : forall s t (t0 : term), P t0 -> P (LamAbs s t t0))
    (H_Apply   : forall t : term, P t -> forall t0 : term, P t0 -> P (Apply t t0))
    (H_Constant : forall (c : constant), P (Constant c))
    (H_Builtin : forall d : DefaultFun, P (Builtin d))
    (H_TyInst  : forall t : term, P t -> forall t0 : ty, P (TyInst t t0))
    (H_Error   : forall t : ty, P (Error t))
    (H_IWrap   : forall (t t0 : ty) (t1 : term), P t1 -> P (IWrap t t0 t1))
    (H_Unwrap  : forall t : term, P t -> P (Unwrap t))
    (H_Constr  : forall (i : nat) T (ts : list (term)), ForallT P ts -> P (Constr i T ts))
    (H_Case   : forall T t, P t -> forall ts, ForallT P ts -> P (Case T t ts)).

  Context
    (H_TermBind    : forall s v t, P t -> Q (TermBind s v t))
    (H_TypeBind    : forall v ty, Q (TypeBind v ty))
    (H_DatatypeBind : forall dtd, Q (DatatypeBind dtd)).

  Context
    (H_cons        : forall b bs, Q b -> R bs -> R (b :: bs))
    (H_nil         : R nil).

  Context
    (H_consS      : forall b bs, Q b -> S bs -> S (b :: bs))
    (H_nilS       : S nil).

  Definition bindings_rect'' (binding_rect'' : forall (b : binding), Q b) :=
    fix bindings_rect'' bs :=
    match bs return R bs with
      | nil       => @H_nil
      | cons b bs => @H_cons _ bs (binding_rect'' b) (bindings_rect'' bs)
    end.

  Definition bindings_nonrect'' (binding_rect'' : forall (b : binding), Q b) :=
    fix bindings_nonrect'' bs :=
    match bs return S bs with
      | nil       => @H_nilS
      | cons b bs => @H_consS _ bs (binding_rect'' b) (bindings_nonrect'' bs)
    end.

  Definition terms_rect'' (term_rect : forall (t : term), P t) :=
    fix terms_rect' ts :=
    match ts as p return ForallT P p with
      | nil       => ForallT_nil
      | cons t ts => ForallT_cons (term_rect t) (terms_rect' ts)
    end.

  Fixpoint term_rect'' (t : term) : P t :=
    match t with
      | Let Rec bs t    => @H_LetRec bs t (bindings_rect'' binding_rect'' bs) (term_rect'' t)
      | Let NonRec bs t => @H_LetNonRec bs t (bindings_nonrect'' binding_rect'' bs) (term_rect'' t)
      | Var n           => @H_Var n
      | TyAbs n k t     => @H_TyAbs n k t (term_rect'' t)
      | LamAbs n ty t   => @H_LamAbs n ty t (term_rect'' t)
      | Apply s t       => @H_Apply s (term_rect'' s) t (term_rect'' t)
      | TyInst t ty     => @H_TyInst t (term_rect'' t) ty
      | IWrap ty1 ty2 t => @H_IWrap ty1 ty2 t (term_rect'' t)
      | Unwrap t        => @H_Unwrap t (term_rect'' t)
      | Error ty        => @H_Error ty
      | Constant c      => @H_Constant c
      | Builtin f       => @H_Builtin f
      | Constr i T ts     => @H_Constr i T ts (terms_rect'' term_rect'' ts)
      | Case T t ts      => @H_Case T t (term_rect'' t) ts (terms_rect'' term_rect'' ts)
    end
  with binding_rect'' (b : binding) : Q b :=
    match b with
      | TermBind s v t   => @H_TermBind s v t (term_rect'' t)
      | TypeBind v ty    => @H_TypeBind v ty
      | DatatypeBind dtd => @H_DatatypeBind dtd
    end.
End term_recursivity_rect.

Lemma constructor_well_formed_sound : 
  forall Δ c T, constructor_well_formed_check Δ c T = true -> Δ |-ok_c c : T.
Proof. 
intros.
destruct c.
inversion H.
remember (splitTy t).
destruct p as [targs tr'].
apply andb_true_iff in H1.
destruct H1.
apply Ty_eqb_eq in H0.
subst.
eapply W_Con.
- eauto.
- simpl in H1.
  intros.
  apply (allb_element_true ty _ _ _ H0) in H1.
  unfold is_KindBase in H1.
  repeat destruct_match.
  subst.
  now apply kind_checking_sound in Heqo.
Qed.

Lemma constructor_well_formed_complete : 
  forall Δ c T, Δ |-ok_c c : T -> constructor_well_formed_check Δ c T = true.
Proof.
  intros.
  destruct c.
  inversion H.
  subst.
  simpl.
  remember (splitTy t) as splitT.
  destruct splitT as [targs' T'].
  inversion H3.
  subst.
  apply andb_true_iff.
  split.
  - apply Ty_eqb_refl.
  - apply allbmap_each.
    intros.
    unfold is_KindBase.
    specialize (H5 b0 H0).
    apply kind_checking_complete in H5.
    rewrite H5.
    reflexivity.
Qed.

Theorem type_checking_sound : 
 forall Δ Γ t ty, type_check Δ Γ t = Some ty -> (Δ ,, Γ |-+ t : ty).
Proof with (try apply kind_checking_sound; try apply normaliser_Jacco_sound; auto).
  intros Δ Γ t ty.
  revert Δ Γ ty.
  eapply term_rect'' with 
    (P := fun t => forall Δ Γ ty, type_check Δ Γ t = Some ty -> Δ,, Γ |-+ t : ty)
    (Q := fun b => forall Δ Γ, binding_well_formed_check type_check Δ Γ b = true -> binding_well_formed Δ Γ b)
    (R := fun bs => forall Δ Γ, bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ) bs = true -> bindings_well_formed_rec Δ Γ bs)
    (S := fun bs => forall Δ Γ, bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ bs = true -> bindings_well_formed_nonrec Δ Γ bs).
    repeat destruct_match.
  - (* Case: Let *)
    intros ec bs t0.
    intros P.
    intros.
      inversion H.
      unfold bind in H1.
      repeat destruct_match.
      eapply T_LetRec.
      * reflexivity.
      * apply map_normaliser_sound. eauto.
      * reflexivity.
      * eapply t0; eauto.
      * eapply P; eauto.
        inversion H1.
        subst.
        auto.
      * 
        inversion H1.
        subst.
        apply kind_checking_sound in Heqo1.
        assumption.
  - (* Case Let NONRec*)
    intros rec bs t0.
    intros P.
    intros.
      inversion H.
      unfold bind in H1.
      repeat destruct_match.
      eapply T_Let with (Δ' := flatten (map binds_Delta rec) ++ Δ).
      * reflexivity.
      * apply map_normaliser_sound. eauto.
      * reflexivity.
      * eapply t0; eauto. 
      * apply P.
        inversion H1.
        subst.
        auto.
      * 
        inversion H1.
        subst.
        apply kind_checking_sound in Heqo1.
        assumption.
  - intros. 
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    (* apply normaliser_Jacco_sound in H1. *)
    eapply T_Var; eauto...
  - intros. 
    inversion H0.
    unfold bind in H0.
    repeat destruct_match.
    inversion H2.
    subst.
    eapply T_TyAbs...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply T_LamAbs...
  - intros.
    inversion H1.
    unfold bind in H3.
    repeat destruct_match.
    inversion H3.
    subst.
    eapply T_Apply.
    + eapply H; eauto.
    + eapply H0; eauto.
      apply Ty_eqb_eq in Heqb.
      now subst.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply T_Constant.
  - intros.
    inversion H.
    unfold bind in H1.
    repeat destruct_match.
    inversion H1; subst.
    apply normaliser_Jacco_sound in Heqo.
    now apply T_Builtin with (T := lookupBuiltinTy d).
  - intros. inversion H0. unfold bind in H2. repeat destruct_match.
    inversion H2. subst.
    apply Kind_eqb_eq in Heqb0.
    subst.
    apply T_TyInst with (X := b) (K2 := k0) (T1n := t3) (T2n := t4)...
  - intros.
    inversion H. subst.
    apply T_Error with (T := Ty_Int).
    + apply K_Builtin.
      apply K_DefaultUniInteger.
    + apply N_TyBuiltin.
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2.
    subst.
    apply Ty_eqb_eq in Heqb0.
    rewrite andb_true_iff in Heqb.
    destruct Heqb as [Heqb1 Heqb2].
    apply Kind_eqb_eq in Heqb1.
    apply Kind_eqb_eq in Heqb2.
    subst.
    apply T_IWrap with (K := k1_5) (T0n := t6)...
  - intros.
    inversion H0.
    unfold bind in H2.
    repeat destruct_match.
    inversion H2. subst.
    apply T_Unwrap with (Fn := t2_1) (Tn := t2_2) (K := k)...
  - intros.
    inversion H.
  - intros.
    inversion H0.
  - intros.
    inversion H0.
    repeat destruct_match.
    subst.
    apply W_Term with (Tn := t3).
    + apply kind_checking_sound in Heqo.
      assumption.
    + now apply normaliser_Jacco_sound in Heqo1.
    + apply Ty_eqb_eq in H2.
      subst.
      eapply H; eauto.
  - intros.
    inversion H.
    repeat destruct_match.
    apply W_Type.
    apply kind_checking_sound in Heqo.
    apply Kind_eqb_eq in H1.
    subst.
    assumption.
  - intros.
    inversion H.
    repeat destruct_match.
    subst.
    eapply W_Data.
    * reflexivity.
    * intros.
      unfold constrLastTyExpected.
      assert (constructor_well_formed_check (rev (map fromDecl l) ++ Δ) c (Ty_Apps (Ty_Var (getTyname t0)) (map (Ty_Var ∘ getTyname) l)) = true).
      { eapply (allb_element_true) in H1.
        - exact H1.
        - assumption.
       }
      now apply constructor_well_formed_sound.
  - intros.
    apply W_ConsB_Rec.
    + apply H.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
    + eapply H0.
      inversion H1.
      apply andb_true_iff in H3.
      destruct H3.
      rewrite H2.
      rewrite H3.
      auto.
  - intros.
    apply W_NilB_Rec.
  - intros.
    inversion H1.
    destruct_match.
    apply andb_true_iff in H3.
    destruct H3.
    eapply W_ConsB_NonRec.
    + apply H.
      assumption.
    + apply map_normaliser_sound in Heqo.
      eauto.
    + apply H0.
      assumption.
  - intros.
    apply W_NilB_NonRec.
Qed.

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
  apply has_type_mut_ind with         
        (P := fun Δ Γ t T _ => type_check Δ Γ t = Some T)
        (P0 := fun Δ Γ l _ => bindings_well_formed_rec_check (binding_well_formed_check type_check Δ Γ) l = true) 
        (P1 := fun Δ Γ l _ => bindings_well_formed_nonrec_check (binding_well_formed_check type_check) Δ Γ l = true )
        (P2 := fun Δ Γ b _ => binding_well_formed_check type_check Δ Γ b = true) 
        ; simpl; auto; intros.
  - (*Case T_Var *)
    rewrite e. simpl. 
    now apply normaliser_Jacco_complete.
  - (* Case: T_LamAbs *)
     apply normaliser_Jacco_complete in n; rewrite n; simpl.
    apply kind_checking_complete in h; rewrite h.
    (* rewrite IHhas_type. Why does this not work?? *)
    now apply test.
  - (* Case: T_Apply *)
    rewrite H0.
    rewrite H1.
    now rewrite -> Ty_eqb_refl.
  - (* Case: T_TyAbs *) 
    now apply oof2.   
  - (* Case: T_Inst *)
    rewrite H0.
    apply kind_checking_complete in h0; rewrite h0.
    rewrite -> Kind_eqb_refl.
    apply normaliser_Jacco_complete in n; rewrite n; simpl.
    now apply normaliser_Jacco_complete in n0; rewrite n0; simpl.
  - (* Case T_IWrap *)
    apply kind_checking_complete in h; rewrite h.
    apply kind_checking_complete in h0; rewrite h0.
    rewrite H0.
    rewrite Kind_eqb_refl; simpl.
    apply normaliser_Jacco_complete in n; rewrite n; simpl.
    apply normaliser_Jacco_complete in n0; rewrite n0; simpl.
    apply normaliser_Jacco_complete in n1; rewrite n1; simpl.
    now rewrite Ty_eqb_refl.
  - (* Case: T_Unwrap*)
    rewrite H0.
    apply kind_checking_complete in h0; rewrite h0.
    now apply normaliser_Jacco_complete in n; rewrite n; simpl.
  - (* Case: T_Builtin*)
    subst.
    now apply normaliser_Jacco_complete in n; rewrite n; simpl.
  - (* Case: T_Error *)
    admit. (* TODO: Not complete in current implementation*)
  - (* Case: T_Let *)
  (* Cas Let NonRec    (* apply map_normaliser_complete in m. *)
    (* In the goal we need things about subterms of bs. That is probably fine here, but I'm not sure why and probably in soundness this will then go wrong?*)
    admit. *)
    apply map_normaliser_complete in m; rewrite m; simpl.
    rewrite H0.
    subst.
    rewrite H1; simpl.
    apply kind_checking_complete in h0; rewrite h0.
    reflexivity.
  - (* Case: T_LetRec *)
    intros. simpl. subst.
    apply map_normaliser_complete in m; rewrite m; simpl.
    rewrite H0.
    rewrite H1.
    simpl.
    apply kind_checking_complete in h0; rewrite h0. auto.
  - (* Case: ? *)
    intros. simpl. rewrite H0. auto.
  - (* Case: ? *)
    apply map_normaliser_complete in m; rewrite m.
    intuition.
  - intros. simpl. rewrite H0.
    apply normaliser_Jacco_complete in n; rewrite n.
    rewrite Ty_eqb_refl.
    apply kind_checking_complete in h; rewrite h.
    auto.
  - intros. simpl. apply kind_checking_complete in h; rewrite h. auto. apply Kind_eqb_eq. reflexivity.
  - intros. simpl. apply allbmap_each with (bs := cs).
    intros.
    specialize (c b H0).
    apply constructor_well_formed_complete in c.
    subst.
    assumption.
Admitted.
    



      
      
      
