Require Import PlutusCert.PlutusIR.
Require Import PlutusCert.Util.List.

Require Export PlutusCert.PlutusIR.Semantics.Static.Auxiliary.
Require Export PlutusCert.PlutusIR.Semantics.Static.Context.
Require Export PlutusCert.PlutusIR.Semantics.Static.Kinding.Kinding.
Require Export PlutusCert.PlutusIR.Semantics.Static.Normalisation.Normalisation.
Require Export PlutusCert.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.PlutusIR.Semantics.Static.Builtins.Signatures.

Import Coq.Lists.List.
Import ListNotations.
Import Coq.Strings.String.
Local Open Scope string_scope.

(* Common built-in types *)
Definition Ty_Int := Ty_Builtin DefaultUniInteger.
Definition Ty_Bool := Ty_Builtin DefaultUniBool.
Definition Ty_String := Ty_Builtin DefaultUniString.
Definition Ty_Unit := Ty_Builtin DefaultUniUnit.
Definition Ty_BS := Ty_Builtin DefaultUniByteString.

Definition Ty_BinOp t := Ty_Fun t (Ty_Fun t t).
Definition Ty_BinPred t := Ty_Fun t (Ty_Fun t Ty_Bool).

(** Types of builtin functions *)
Definition lookupBuiltinTy f := to_ty (to_sig f).


(** Helper funcitons*)
Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

Open Scope list_scope.
Lemma flatten_cons {A} x (xs : list (list A)) :
  flatten (x :: xs) = flatten xs ++ x.
Proof.
  unfold flatten. simpl.
  rewrite concat_app. simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Fixpoint splitTy (T : ty) : list ty * ty :=
  match T with
  | Ty_Fun Targ T' => (cons Targ (fst (splitTy T')), snd (splitTy T'))
  | Tr => (nil, Tr)
  end.

Definition fromDecl (tvd : tvdecl) : string * kind :=
  match tvd with
  | TyVarDecl v K => (v, K)
  end.

(* TODO:

well-kinded?
normalisation preserves kinding.
T has kind K 
F has kind (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base))

(Ty_IFix F (Ty_Var "X") has kind Kind_Base if (Ty_Var "X") has kind K.

Then (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X"))) has kind (Kind_Arrow K Kind_Base)

We apply F to this type to get the same kind back (see kind F), so then we have
(Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) has kind (Kind_Arrow K Kind_Base)

T has kind K, so this is well kinded with kind Kind_Base and for every context.
*)
Definition unwrapIFix (F : ty) (K : kind) (T : ty) : ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

(** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0, no associativity).
Reserved Notation "Delta '|-ok_c' c ':' T" (at level 101, c at level 0, T at level 0).
Reserved Notation "Delta ',,' Gamma  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Delta ',,' Gamma '|-ok_b' b" (at level 101, b at level 0, no associativity).

Local Open Scope list_scope.

Fixpoint insert_deltas_rec (xs : list (string * ty)) (Δ : list (string * kind)) := 
match xs with
  | nil => nil
  | (x, T) :: xs' => (x, T, Δ) :: insert_deltas_rec xs' Δ
end.


Inductive has_type : list (string * kind) -> list (string * ty) -> term -> ty -> Prop :=
  (* Simply typed lambda caclulus *)
  | T_Var : forall Γ Δ x T Tn K,
      lookup x Γ = Coq.Init.Datatypes.Some T ->
      Δ |-* T : K -> (* Added *)
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
      ((X, K2)::Δ) |-* T1n : Kind_Base -> (* Added *)
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
      Δ |-* Fn : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) -> (* Added *)
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
      normalise T Tn -> (* S Sn (denk aan preservation. T Tn hadden we geimplementeerd omdat dat makkelijk is voor preservation mss, maar dat werkt niet voor completeness ), maak pull request*)
      Δ ,, Γ |-+ (Error S) : Tn
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module PlutusIR.TypeCheck.Internal in the
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_wk (insert_deltas_rec (flatten (map binds_Gamma bs)) Δ) -> (* Why these deltas? Seems too strict, what about Δ' *)
      map_normalise (flatten (map binds_Gamma bs)) bsGn ->
      Γ' = bsGn ++ Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t : Tn ->
      Δ |-* Tn : Kind_Base ->
      Δ ,, Γ |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Δ Γ bs t Tn Δ' Γ' bsGn,
      Δ' = flatten (map binds_Delta bs) ++ Δ ->
      map_wk (insert_deltas_rec (flatten (map binds_Gamma bs)) Δ') -> (* Why these deltas? *)
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
      map_wk (insert_deltas_rec (binds_Gamma b) (Δ)) -> (* Just Δ? Or binds_Delta b?*)
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

Lemma lookupBuiltinTy__well_kinded f Δ :
  Δ |-* (lookupBuiltinTy f) : Kind_Base.
Admitted.


Definition well_typed t := exists T, [] ,, [] |-+ t : T.

Lemma T_Let__cons Δ Γ Γ_b b bs t Tn :
  Δ ,, Γ |-ok_b b ->
  Δ |-* Tn : Kind_Base -> (* Tn may not mention types bound in b (escaping) *)
  map_normalise (binds_Gamma b) Γ_b ->
  binds_Delta b ++ Δ ,, Γ_b ++ Γ |-+ (Let NonRec bs t) : Tn ->
  Δ ,, Γ |-+ (Let NonRec (b :: bs) t) : Tn
.
Proof.
  intros H_typing_b H_kind H_mn H_ty.
  inversion H_ty; subst.

  econstructor.
  - exact eq_refl.
  - unfold flatten.
    simpl.
    rewrite concat_app.
    simpl.
    rewrite app_nil_r.
    (* apply MN_app.
    + eassumption.
    + eassumption.
  - exact eq_refl.
  - econstructor.
    + assumption.
    + eassumption.
    + eassumption.
  - simpl.
    rewrite flatten_cons.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    assumption.
  - assumption. *)
Admitted.

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
Inductive context_has_type : list (string * kind) -> list (string * ty) -> context -> ((list (string * kind)) * list (string * ty) * ty) -> ty -> Prop :=

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
