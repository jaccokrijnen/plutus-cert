Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.
Import NamedTerm.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.

Import Coq.Lists.List.
Import ListNotations.
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

Definition fromDecl (tvd : tvdecl string) : string * Kind :=
  match tvd with
  | TyVarDecl v K => (v, K)
  end.

Definition unwrapIFix (F : Ty) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

Inductive has_type : list (string * Kind) -> list (string * Ty) -> Term -> Ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Gamma Delta x T Tn,
      lookup x Gamma = Coq.Init.Datatypes.Some T ->
      normalise T Tn ->
      Delta ,, Gamma |-+ (Var x) : Tn
  | T_LamAbs : forall Delta Gamma x T1 t T2n T1n,
      Delta |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Delta ,, (x, T1n) :: Gamma |-+ t : T2n ->
      Delta ,, Gamma |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Delta Gamma t1 t2 T1n T2n,
      Delta ,, Gamma |-+ t1 : (Ty_Fun T1n T2n) ->
      Delta ,, Gamma |-+ t2 : T1n ->
      Delta ,, Gamma |-+ (Apply t1 t2) : T2n
  (* Universal types *)
  | T_TyAbs : forall Delta Gamma X K t Tn,
      ((X, K) :: Delta) ,, Gamma |-+ t : Tn ->
      Delta ,, Gamma |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_TyInst : forall Delta Gamma t1 T2 T1n X K2 T0n T2n,
      Delta ,, Gamma |-+ t1 : (Ty_Forall X K2 T1n) ->
      Delta |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Delta ,, Gamma |-+ (TyInst t1 T2) : T0n
  (* Recursive types *)
  | T_IWrap : forall Delta Gamma F T M K Tn Fn T0n,
      Delta |-* T : K ->
      normalise T Tn ->
      Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Delta ,, Gamma |-+ M : T0n ->
      Delta ,, Gamma |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Delta Gamma M Fn K Tn T0n,
      Delta ,, Gamma |-+ M : (Ty_IFix Fn Tn) ->
      Delta |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Delta ,, Gamma |-+ (Unwrap M) : T0n
  (* Additional constructs *)
  | T_Constant : forall Delta Gamma u a,
      Delta ,, Gamma |-+ (Constant (Some (ValueOf u a))) : (Ty_Builtin (Some (TypeIn u)))
  | T_Builtin : forall Delta Gamma f T Tn,
      T = lookupBuiltinTy f ->
      normalise T Tn ->
      Delta ,, Gamma |-+ (Builtin f) : Tn
  | T_Error : forall Delta Gamma S T Tn,
      Delta |-* T : Kind_Base ->
      normalise T Tn ->
      Delta ,, Gamma |-+ (Error S) : Tn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Delta Gamma bs t Tn Delta' Gamma' bsGn,
      Delta' = flatten (map binds_Delta bs) ++ Delta ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Gamma' = bsGn ++ Gamma ->
      Delta ,, Gamma |-oks_nr bs ->
      Delta' ,, Gamma' |-+ t : Tn ->
      Delta |-* Tn : Kind_Base ->
      Delta ,, Gamma |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Delta Gamma bs t Tn Delta' Gamma' bsGn,
      Delta' = flatten (map binds_Delta bs) ++ Delta ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Gamma' = bsGn ++ Gamma->
      Delta' ,, Gamma' |-oks_r bs ->
      Delta' ,, Gamma' |-+ t : Tn ->
      Delta |-* Tn : Kind_Base ->
      Delta ,, Gamma |-+ (Let Rec bs t) : Tn

with constructor_well_formed : list (string * Kind) -> constructor -> Ty -> Prop :=
  | W_Con : forall Delta x T ar Targs Tr,
      (Targs, Tr) = splitTy T ->
      (forall U, In U Targs -> Delta |-* U : Kind_Base) ->
      Delta |-ok_c (Constructor (VarDecl x T) ar) : Tr

with bindings_well_formed_nonrec : list (string * Kind) -> list (string * Ty) -> list Binding -> Prop :=
  | W_NilB_NonRec : forall Delta Gamma,
      Delta ,, Gamma |-oks_nr nil
  | W_ConsB_NonRec : forall Delta Gamma b bs bsGn,
      Delta ,, Gamma |-ok_b b ->
      map_normalise (binds_Gamma b) bsGn ->
      ((binds_Delta b) ++ Delta) ,, (bsGn ++ Gamma) |-oks_nr bs ->
      Delta ,, Gamma |-oks_nr (b :: bs)

with bindings_well_formed_rec : list (string * Kind) -> list (string * Ty) -> list Binding -> Prop :=
  | W_NilB_Rec : forall Delta Gamma,
      Delta ,, Gamma |-oks_r nil
  | W_ConsB_Rec : forall Delta Gamma b bs,
      Delta ,, Gamma |-ok_b b ->
      Delta ,, Gamma |-oks_r bs ->
      Delta ,, Gamma |-oks_r (b :: bs)

with binding_well_formed : list (string * Kind) -> list (string * Ty) -> Binding -> Prop :=
  | W_Term : forall Delta Gamma s x T t Tn,
      Delta |-* T : Kind_Base ->
      normalise T Tn ->
      Delta ,, Gamma |-+ t : Tn ->
      Delta ,, Gamma |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall Delta Gamma X K T,
      Delta |-* T : K ->
      Delta ,, Gamma |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall Delta Gamma X YKs cs matchFunc Delta',
      Delta' = rev (map fromDecl YKs) ++ Delta ->
      (forall c, In c cs -> Delta' |-ok_c c : (constrLastTy (Datatype X YKs matchFunc cs))) ->
      Delta ,, Gamma |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Delta ',,' Gamma '|-+' t ':' T" := (has_type Delta Gamma t T)
  and  "Delta '|-ok_c' c ':' T" := (constructor_well_formed Delta c T)
  and "Delta ',,' Gamma '|-oks_nr' bs" := (bindings_well_formed_nonrec Delta Gamma bs)
  and "Delta ',,' Gamma '|-oks_r' bs" := (bindings_well_formed_rec Delta Gamma bs)
  and "Delta ',,' Gamma '|-ok_b' b" := (binding_well_formed Delta Gamma b).

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

Definition well_typed t := exists T, [] ,, [] |-+ t : T.

Lemma has_type__normal : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros; eauto using normalise_to_normal...
  - inversion IHhas_type1; subst...
    inversion H1.
Qed.



(* Notation for types of holes *)
Notation "Δ ',,' Γ '▷' T" := (Δ, Γ, T) (at level 101).

Reserved Notation "Δ₁ ',,' Γ₁ '|-C' C ':' HTy ↝ T₁" (at level 101, C at level 0, T₁ at level 0, no associativity).

(* Typing rules for one-hole contexts *)
Inductive context_has_type : list (string * Kind) -> list (string * Ty) -> Context -> ((list (string * Kind)) * list (string * Ty) * Ty) -> Ty -> Prop :=

  | T_C_Hole : forall Δ Γ Tn,
      normal_Ty Tn ->
      Δ ,, Γ |-C C_Hole : (Δ ,, Γ ▷ Tn) ↝ Tn

  | T_C_LamAbs : forall Δ₁ Γ₁ x T1 C Δ Γ Tn T2n T1n,
      Δ₁ |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Δ₁ ,, (x, T1n) :: Γ₁ |-C C                 : (Δ ,, Γ ▷ Tn) ↝ T2n ->
      Δ₁ ,,             Γ₁ |-C (C_LamAbs x T1 C) : (Δ ,, Γ ▷ Tn) ↝ (Ty_Fun T1n T2n)

  | T_C_Apply_L : forall Δ₁ Γ₁ Δ Γ C t Tn T1n T2n,
      Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ Tn) ↝ (Ty_Fun T1n T2n) ->
      Δ₁ ,, Γ₁ |-+ t : T1n ->
      Δ₁ ,, Γ₁ |-C (C_Apply_L C t) : (Δ ,, Γ ▷ Tn) ↝ T2n

  | T_C_Apply_R : forall Δ₁ Γ₁ Δ Γ C t Tn T1n T2n,
      Δ₁ ,, Γ₁ |-+ t : (Ty_Fun T1n T2n) ->
      Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ Tn) ↝ T1n ->
      Δ₁ ,, Γ₁ |-C (C_Apply_R t C) : (Δ ,, Γ ▷ Tn) ↝ T2n

  where
    "Δ₁ ',,' Γ₁ '|-C' C ':' Hty ↝ T₁" := (context_has_type Δ₁ Γ₁ C Hty T₁)
.

Lemma context_has_type__normal : forall Δ₁ Γ₁ C Δ Γ T T₁,
    Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
    normal_Ty T₁.
Proof with eauto using normalise_to_normal.
  intros Δ₁ Γ₁ C Δ Γ T T₁ Cty.
  induction Cty...

  (* C_App_L *)
  - inversion IHCty...
    (* NO_Neutral *)
    + inversion H0.

  (* C_App_R *)
  - apply has_type__normal in H.
    inversion H...
    (* NO_Neutral *)
    + inversion H0.
Qed.

Lemma context_has_type__hole_normal : forall Δ₁ Γ₁ C Δ Γ T T₁,
    Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁ ->
    normal_Ty T.
Proof.
  intros Δ₁ Γ₁ C Δ Γ T T₁ Cty.
  Require Import Coq.Program.Equality.
  dependent induction Cty.
  all: eauto.
Qed.


Lemma context_has_type__apply : forall C t Δ₁ Γ₁ Δ Γ T T₁,
  (Δ₁ ,, Γ₁ |-C C : (Δ ,, Γ ▷ T) ↝ T₁) ->
  (Δ ,, Γ |-+ t : T) ->
  (Δ₁ ,, Γ₁ |-+ (context_apply C t) : T₁).
Admitted.
