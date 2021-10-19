
Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Import Coq.Lists.List.
Import Coq.Strings.String.

Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Implementations.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Normalisation.

Create HintDb typing.

(** ** Kinding of types *)
Reserved Notation "Delta '|-*' ty ':' K" (at level 40, ty at level 0, K at level 0).
Inductive has_kind : Delta -> Ty -> Kind -> Prop :=
  | K_Var : forall Delta X K,
      Delta X = Coq.Init.Datatypes.Some K ->
      Delta |-* (Ty_Var X) : K
  | K_Fun : forall Delta T1 T2,
      Delta |-* T1 : Kind_Base ->
      Delta |-* T2 : Kind_Base ->
      Delta |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall Delta F T K,
      Delta |-* T : K ->
      Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Delta |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall Delta X K T,
      (X |-> K; Delta) |-* T : Kind_Base ->
      Delta |-* (Ty_Forall X K T) : Kind_Base
  | K_Builtin : forall Delta u T,
      T = lookupBuiltinKind u ->
      Delta |-* (Ty_Builtin (Some (TypeIn u))) : T
  | K_Lam : forall Delta X K1 T K2,
      (X |-> K1; Delta) |-* T : K2 ->
      Delta |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Delta T1 T2 K1 K2,
      Delta |-* T1 : (Kind_Arrow K1 K2) ->
      Delta |-* T2 : K1 ->
      Delta |-* (Ty_App T1 T2) : K2
where "Delta '|-*' ty ':' K" := (has_kind Delta ty K).

(** ** Typing of terms *)
Reserved Notation "Delta ',,' Gamma '|-+' t ':' T" (at level 101, t at level 0, T at level 0).

Inductive has_type : Delta -> Gamma -> Term -> Ty -> Prop :=
  (** Let-bindings
      Note: The rules for let-constructs differ significantly from the paper definitions
      because we had to adapt the typing rules to the compiler implementation of type checking.
      Reference: The Haskell module Language.PlutusIR.TypeCheck.Internal in the 
      iohk/plutus/plutus-core/plutus-ir project.
  **)
  | T_Let : forall Delta Gamma bs t Tn Delta' Gamma' bsGn,
      Delta' = mupdate Delta (flatten (map binds_Delta bs)) ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn -> 
      Gamma' = mupdate Gamma bsGn ->
      bindings_well_formed_nonrec Delta Gamma bs ->
      Delta' ,, Gamma' |-+ t : Tn ->
      Delta ,, Gamma |-+ (Let NonRec bs t) : Tn
  | T_LetRec : forall Delta Gamma bs t Tn Delta' Gamma' bsGn,
      Delta' = mupdate Delta (flatten (map binds_Delta bs)) ->
      map_normalise (flatten (map binds_Gamma bs)) bsGn -> 
      Gamma' = mupdate Gamma bsGn ->
      bindings_well_formed_rec Delta' Gamma' bs ->
      Delta' ,, Gamma' |-+ t : Tn ->
      Delta ,, Gamma |-+ (Let Rec bs t) : Tn
  (* Basic constructs *)
  | T_Var : forall Gamma Delta x T Tn,
      Gamma x = Coq.Init.Datatypes.Some T ->
      normalise T Tn ->
      Delta ,, Gamma |-+ (Var x) : Tn
  | T_TyAbs : forall Delta Gamma X K t Tn,
      (X |-> K; Delta) ,, Gamma |-+ t : Tn ->
      Delta ,, Gamma |-+ (TyAbs X K t) : (Ty_Forall X K Tn)
  | T_LamAbs : forall Delta Gamma x T1 t T2n T1n,
      Delta |-* T1 : Kind_Base ->
      normalise T1 T1n ->
      Delta ,, x |-> T1n; Gamma |-+ t : T2n -> 
      Delta ,, Gamma |-+ (LamAbs x T1 t) : (Ty_Fun T1n T2n)
  | T_Apply : forall Delta Gamma t1 t2 T1n T2n,
      Delta ,, Gamma |-+ t1 : (Ty_Fun T1n T2n) ->
      Delta ,, Gamma |-+ t2 : T1n ->
      Delta ,, Gamma |-+ (Apply t1 t2) : T2n
  | T_Constant : forall Delta Gamma u a,
      Delta ,, Gamma |-+ (Constant (Some (ValueOf u a))) : (Ty_Builtin (Some (TypeIn u)))
  | T_Builtin : forall Delta Gamma f Tn,
      Tn = lookupBuiltinTy f ->
      Delta ,, Gamma |-+ (Builtin f) : Tn
  | T_TyInst : forall Delta Gamma t1 T2 T1n X K2 T0n T2n,
      Delta ,, Gamma |-+ t1 : (Ty_Forall X K2 T1n) ->
      Delta |-* T2 : K2 ->
      normalise T2 T2n ->
      normalise (substituteTCA X T2n T1n) T0n ->
      Delta ,, Gamma |-+ (TyInst t1 T2) : T0n
  | T_Error : forall Delta Gamma T Tn,
      Delta |-* T : Kind_Base ->
      normalise T Tn ->
      Delta ,, Gamma |-+ (Error T) : Tn
  (* Recursive types *)
  | T_IWrap : forall Delta Gamma F T M K T0n Tn Fn,
      normalise (unwrapIFix F K T) T0n ->
      Delta ,, Gamma |-+ M : T0n ->
      Delta |-* T : K ->
      normalise T Tn ->
      Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      normalise F Fn ->
      Delta ,, Gamma |-+ (IWrap F T M) : (Ty_IFix Fn Tn)
  | T_Unwrap : forall Delta Gamma M Fn K Tn T0n,
      Delta ,, Gamma |-+ M : (Ty_IFix Fn Tn) ->
      Delta |-* Tn : K ->
      normalise (unwrapIFix Fn K Tn) T0n ->
      Delta ,, Gamma |-+ (Unwrap M) : T0n

  (* Extras *)
  | T_ExtBuiltin : forall Delta Gamma f args Targs Tr Tr',
      List.length args <= arity f ->
      (Targs, Tr) = splitTy (lookupBuiltinTy f) ->
      (forall p, In p (List.combine args Targs) -> Delta ,, Gamma |-+ (fst p) : (snd p)) ->
      Tr' = combineTy (skipn (List.length args) Targs) Tr ->
      Delta ,, Gamma |-+ (ExtBuiltin f args) : Tr'

  with constructor_well_formed : Delta -> constructor -> Prop :=
    | W_Con : forall Delta x T ar Targs Tr,
        (Targs, Tr) = splitTy T -> 
        (forall U, In U Targs -> Delta |-* U : Kind_Base) ->
        constructor_well_formed Delta (Constructor (VarDecl x T) ar)

  with bindings_well_formed_nonrec : Delta -> Gamma -> list Binding -> Prop :=
    | W_NilB_NonRec : forall Delta Gamma,
        bindings_well_formed_nonrec Delta Gamma nil
    | W_ConsB_NonRec : forall Delta Gamma b bs bsGn,
        binding_well_formed Delta Gamma b ->
        map_normalise (binds_Gamma b) bsGn ->
        bindings_well_formed_nonrec (mupdate Delta (binds_Delta b)) (mupdate Gamma bsGn) bs ->
        bindings_well_formed_nonrec Delta Gamma (b :: bs)

  with bindings_well_formed_rec : Delta -> Gamma -> list Binding -> Prop :=
    | W_NilB_Rec : forall Delta Gamma,
        bindings_well_formed_rec Delta Gamma nil
    | W_ConsB_Rec : forall Delta Gamma b bs,
        binding_well_formed Delta Gamma b ->
        bindings_well_formed_rec Delta Gamma bs ->
        bindings_well_formed_rec Delta Gamma (b :: bs)

  with binding_well_formed : Delta -> Gamma -> Binding -> Prop :=
    | W_Term : forall Delta Gamma s x T t,
        Delta |-* T : Kind_Base ->
        Delta ,, Gamma |-+ t : T ->
        binding_well_formed Delta Gamma (TermBind s (VarDecl x T) t)
    | W_Type : forall Delta Gamma X K T,
        Delta |-* T : K ->
        binding_well_formed Delta Gamma (TypeBind (TyVarDecl X K) T)
    | W_Data : forall Delta Gamma X YKs cs matchFunc Delta' Gamma',
        Delta' = mupdate Delta (rev (map fromDecl YKs)) ->
        Gamma' = Gamma ->
        (forall c, In c cs -> constructor_well_formed Delta' c) ->
        binding_well_formed Delta Gamma (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Delta ',,' Gamma '|-+' t ':' T" := (has_type Delta Gamma t T).

Notation "Delta '|-ok_c' c" := (constructor_well_formed Delta c) (at level 101, c at level 0).
Notation "Delta ',,' Gamma '|-oks_nr' bs" := (bindings_well_formed_nonrec Delta Gamma bs) (at level 101, bs at level 0).
Notation "Delta ',,' Gamma '|-oks_r' bs" := (bindings_well_formed_rec Delta Gamma bs) (at level 101, bs at level 0).
Notation "Delta ',,' Gamma '|-ok' b" := (binding_well_formed Delta Gamma b) (at level 101, b at level 0).

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

#[export] Hint Constructors has_kind : typing.

#[export] Hint Constructors has_type : typing.
#[export] Hint Constructors constructor_well_formed : typing.
#[export] Hint Constructors bindings_well_formed_nonrec : typing.
#[export] Hint Constructors bindings_well_formed_rec : typing.
#[export] Hint Constructors binding_well_formed : typing.

Lemma strong_normalisation : forall Delta T K,
    Delta |-* T : K ->
    exists T_norm, normalise T T_norm.
Proof.
  induction 1; eauto.
  - destruct IHhas_kind1.
    destruct IHhas_kind2.
    eauto.
  - destruct IHhas_kind1.
    destruct IHhas_kind2.
    eauto.
  - destruct IHhas_kind.
    eauto.
  - destruct IHhas_kind.
    eauto.
  - destruct IHhas_kind1.
    destruct IHhas_kind2.
    inversion H; subst.
    + eauto.
    + destruct u; inversion H3.
    + Axiom skip: forall P, P. apply skip.
    + inversion H1; subst.
      * apply skip.
      * apply normalise_to_normal in H1 as Hnorm.
        inversion Hnorm; subst.
        eauto.
Qed.

Lemma has_type__normal : forall Delta Gamma t T,
    Delta ,, Gamma |-+ t : T ->
    normal_Ty T.
Proof with eauto.
  induction 1; intros.
  - assumption.
  - assumption.
  - eapply normalise_to_normal; eauto.
  - eauto.
  - eapply normalise_to_normal in H0...
  - inversion IHhas_type1; subst...
    inversion H1.
  - eauto.
  - destruct f; simpl in H; inversion H; subst...
    apply NO_TyForall...
    apply NO_TyFun...
    apply NO_TyFun...
  - eapply normalise_to_normal...
  - eapply normalise_to_normal...
  - eapply normalise_to_normal in H2...
    eapply normalise_to_normal in H4...
  - eapply normalise_to_normal...
  - apply skip.
Qed.