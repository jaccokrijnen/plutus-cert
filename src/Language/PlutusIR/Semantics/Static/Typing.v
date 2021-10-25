Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Normalisation.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.

Import Coq.Lists.List.
Import Coq.Strings.String.
Local Open Scope string_scope.

(** Types of builtin functions *)
Definition lookupBuiltinTy (f : DefaultFun) : Ty :=
  let Ty_Int := Ty_Builtin (Some (TypeIn DefaultUniInteger)) in
  let Ty_Bool := Ty_Builtin (Some (TypeIn DefaultUniBool)) in
  let Ty_BS := Ty_Builtin (Some (TypeIn DefaultUniByteString)) in
  let T_Int_Bin := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Int) in
  let T_Int_BinPredicate := Ty_Fun Ty_Int (Ty_Fun Ty_Int Ty_Bool) in
  let T_BS_Bin := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_BS) in
  let T_BS_BinPredicate := Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool) in
  let Ty_Char := Ty_Builtin (Some (TypeIn DefaultUniChar)) in
  let Ty_String := Ty_Builtin (Some (TypeIn DefaultUniString)) in
  let Ty_Unit := Ty_Builtin (Some (TypeIn DefaultUniUnit)) in
  match f with
  | AddInteger => T_Int_Bin
  | SubtractInteger => T_Int_Bin
  | MultiplyInteger => T_Int_Bin
  | DivideInteger => T_Int_Bin
  | QuotientInteger => T_Int_Bin
  | RemainderInteger => T_Int_Bin
  | ModInteger => T_Int_Bin
  | LessThanInteger => T_Int_BinPredicate
  | LessThanEqInteger => T_Int_BinPredicate
  | GreaterThanInteger => T_Int_BinPredicate
  | GreaterThanEqInteger => T_Int_BinPredicate
  | EqInteger => T_Int_BinPredicate
  | Concatenate => T_BS_Bin
  | TakeByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | DropByteString => Ty_Fun Ty_Int (Ty_Fun Ty_BS Ty_BS)
  | SHA2 => Ty_Fun Ty_BS Ty_BS
  | SHA3 => Ty_Fun Ty_BS Ty_BS
  | VerifySignature => Ty_Fun Ty_BS (Ty_Fun Ty_BS (Ty_Fun Ty_BS Ty_Bool))
  | EqByteString => T_BS_BinPredicate
  | LtByteString => T_BS_BinPredicate
  | GtByteString => T_BS_BinPredicate
  | IfThenElse => Ty_Forall "a" Kind_Base (Ty_Fun Ty_Bool (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "a") (Ty_Var "a"))))
  | CharToString => Ty_Fun Ty_Char Ty_String
  | Append => Ty_Fun Ty_String (Ty_Fun Ty_String Ty_String)
  | Trace => Ty_Fun Ty_String Ty_Unit (* TODO: figure out if it is the correct type*)
  end.

(** Helper funcitons*)
Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Fixpoint splitTy (T : Ty) : list Ty * Ty :=
  match T with
  | Ty_Fun Targ T' => (cons Targ (fst (splitTy T')), snd (splitTy T'))
  | Tr => (nil, Tr)
  end.

Definition fromDecl (tvd : tvdecl tyname) : tyname * Kind :=
  match tvd with
  | TyVarDecl v K => (v, K)   
  end.
    
Definition unwrapIFix (F : Ty) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma ';;' flag '|-+' t ':' T" (at level 101, flag at level 0, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma ';;' flag '|-oks_nr' bs" (at level 101, flag at level 0, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma ';;' flag '|-oks_r' bs" (at level 101, flag at level 0, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma ';;' flag '|-ok_b' b" (at level 101, flag at level 0, b at level 0, no associativity).

Inductive TypingFlag : Type := | Escape | NoEscape .

Inductive has_type : TypingFlag -> Delta -> Gamma -> Term -> Ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Gamma Delta x T Tn flag,
      Gamma x = Coq.Init.Datatypes.Some T ->
      normalise T Tn ->
      Delta ,, Gamma ;; flag |-+ (Var x) : Tn
  | T_LamAbs : forall Delta Gamma x T1 t T2n T1n flag,
      Delta |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Delta ,, x |-> T1n; Gamma ;; flag |-+ t : T2n -> 
      Delta ,, Gamma ;; flag |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Delta Gamma t1 t2 T1n T2n flag,
      Delta ,, Gamma ;; flag |-+ t1 : (Ty_Fun T1n T2n) ->
      Delta ,, Gamma ;; flag |-+ t2 : T1n ->
      Delta ,, Gamma ;; flag |-+ (Apply t1 t2) : T2n
  (* Universal quantification*)
  | T_TyAbs : forall Delta Gamma X K t Tn flag,
      (X |-> K; Delta) ,, Gamma ;; flag |-+ t : Tn ->
      Delta ,, Gamma ;; flag |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Delta Gamma t1 T2 T1n X K2 T0n T2n flag,
      Delta ,, Gamma ;; flag |-+ t1 : (Ty_Forall X K2 T1n) ->
      Delta |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Delta ,, Gamma ;; flag |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Delta Gamma F T M K Tn Fn T0n flag,
      Delta |-* T : K ->
      normalise T Tn ->
      Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Delta ,, Gamma ;; flag |-+ M : T0n ->
      Delta ,, Gamma ;; flag |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Delta Gamma M Fn K Tn T0n flag,
      Delta ,, Gamma ;; flag |-+ M : (Ty_IFix Fn Tn) ->
      Delta |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Delta ,, Gamma ;; flag |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Delta Gamma u a flag,
      Delta ,, Gamma ;; flag |-+ (Constant (Some (ValueOf u a))) : (Ty_Builtin (Some (TypeIn u)))
  | T_Builtin : forall Delta Gamma f T Tn flag,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Delta ,, Gamma ;; flag |-+ (Builtin f) : Tn
  | T_Error : forall Delta Gamma S T Tn flag,
      Delta |-* T : Kind_Base ->
      normalise T Tn ->
      Delta ,, Gamma ;; flag |-+ (Error S) : Tn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module Language.PlutusIR.TypeCheck.Internal in the 
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Delta Gamma bs t Tn Delta' Gamma' bsGn flag,
      Delta' = mupdate Delta (flatten (map binds_Delta bs)) ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn -> 
      Gamma' = mupdate Gamma bsGn ->
      Delta ,, Gamma ;; flag |-oks_nr bs ->
      Delta' ,, Gamma' ;; flag |-+ t : Tn ->
      (flag = NoEscape -> Delta |-* Tn : Kind_Base) ->
      Delta ,, Gamma ;; flag |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Delta Gamma bs t Tn Delta' Gamma' bsGn flag,
      Delta' = mupdate Delta (flatten (map binds_Delta bs)) ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn -> 
      Gamma' = mupdate Gamma bsGn ->
      Delta' ,, Gamma' ;; flag |-oks_r bs ->
      Delta' ,, Gamma' ;; flag |-+ t : Tn ->
      (flag = NoEscape -> Delta |-* Tn : Kind_Base) ->
      Delta ,, Gamma ;; flag |-+ (Let Rec bs t) : Tn

  with constructor_well_formed : Delta -> constructor -> Ty -> Prop :=
    | W_Con : forall Delta x T ar Targs Tr,
        (Targs, Tr) = splitTy T -> 
        (forall U, In U Targs -> Delta |-* U : Kind_Base) ->
        Delta |-ok_c (Constructor (VarDecl x T) ar) : Tr

  with bindings_well_formed_nonrec : TypingFlag -> Delta -> Gamma -> list Binding -> Prop :=
    | W_NilB_NonRec : forall Delta Gamma flag,
      Delta ,, Gamma ;; flag |-oks_nr nil
    | W_ConsB_NonRec : forall Delta Gamma b bs bsGn flag,
        Delta ,, Gamma ;; flag |-ok_b b ->
        map_normalise (binds_Gamma b) bsGn ->
        (mupdate Delta (binds_Delta b)) ,, (mupdate Gamma bsGn) ;; flag |-oks_nr bs ->
        Delta ,, Gamma ;; flag |-oks_nr (b :: bs)

  with bindings_well_formed_rec : TypingFlag -> Delta -> Gamma -> list Binding -> Prop :=
    | W_NilB_Rec : forall Delta Gamma flag,
        Delta ,, Gamma ;; flag |-oks_r nil
    | W_ConsB_Rec : forall Delta Gamma b bs flag,
        Delta ,, Gamma ;; flag |-ok_b b ->
        Delta ,, Gamma ;; flag |-oks_r bs ->
        Delta ,, Gamma ;; flag |-oks_r (b :: bs)

  with binding_well_formed : TypingFlag -> Delta -> Gamma -> Binding -> Prop :=
    | W_Term : forall Delta Gamma s x T t Tn flag,
        Delta |-* T : Kind_Base ->
        normalise T Tn ->
        Delta ,, Gamma ;; NoEscape |-+ t : Tn ->
        Delta ,, Gamma ;; flag |-ok_b (TermBind s (VarDecl x T) t)
    | W_Type : forall Delta Gamma X K T flag,
        Delta |-* T : K ->
        Delta ,, Gamma ;; flag |-ok_b (TypeBind (TyVarDecl X K) T)
    | W_Data : forall Delta Gamma X YKs cs matchFunc Delta' flag,
        Delta' = mupdate Delta (rev (map fromDecl YKs)) ->
        (forall c, In c cs -> Delta' |-ok_c c : (constrLastTy (Datatype X YKs matchFunc cs))) ->
        Delta ,, Gamma ;; flag |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Delta ',,' Gamma ';;' flag '|-+' t ':' T" := (has_type flag Delta Gamma t T)
  and  "Delta '|-ok_c' c ':' T" := (constructor_well_formed Delta c T)
  and "Delta ',,' Gamma ';;' flag '|-oks_nr' bs" := (bindings_well_formed_nonrec flag Delta Gamma bs)
  and "Delta ',,' Gamma ';;' flag '|-oks_r' bs" := (bindings_well_formed_rec flag Delta Gamma bs)
  and "Delta ',,' Gamma ';;' flag '|-ok_b' b" := (binding_well_formed flag Delta Gamma b).

Scheme has_type__ind := Minimality for has_type Sort Prop
  with constructor_well_formed__ind := Minimality for constructor_well_formed Sort Prop
  with bindings_well_formed_nonrec__ind := Minimality for bindings_well_formed_nonrec Sort Prop
  with bindings_well_formed_rec__ind := Minimality for bindings_well_formed_rec Sort Prop
  with binding_well_formed__ind := Minimality for binding_well_formed Sort Prop.

Combined Scheme has_type__multind from 
  has_type__ind,
  bindings_well_formed_nonrec__ind,
  bindings_well_formed_rec__ind,
  binding_well_formed__ind.

Lemma has_type__normal : forall Delta Gamma flag t T,
    Delta ,, Gamma ;; flag |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros; eauto using normalise_to_normal...
  - inversion IHhas_type1; subst...
    inversion H1.
Qed.

Lemma typing_subsumes_escaped_typing : 
  (forall flag Delta Gamma t T, Delta ,, Gamma ;; flag |-+ t : T -> 
    (Delta ,, Gamma ;; Escape |-+ t : T)) /\
  (forall flag Delta Gamma bs, Delta ,, Gamma ;; flag |-oks_nr bs ->
    (Delta ,, Gamma ;; Escape |-oks_nr bs)) /\
  (forall flag Delta Gamma bs, Delta ,, Gamma ;; flag |-oks_r bs ->
    (Delta ,, Gamma ;; Escape |-oks_r bs)) /\
  (forall flag Delta Gamma b, Delta ,, Gamma ;; flag |-ok_b b ->
    (Delta ,, Gamma ;; Escape |-ok_b b)).
Proof with eauto.
  apply has_type__multind
    with (P0 := fun (Delta : Delta) (c : constructor) (T : Ty) => True).
  all: intros.
  all: try (destruct flag).
  all: try solve [econstructor; eauto].
Qed.