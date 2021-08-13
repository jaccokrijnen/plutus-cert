Require Export PlutusCert.Language.PlutusIR.
(* Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Context. *)



Section Typing.

Import Coq.Lists.List.
Import Coq.Strings.String.
Local Open Scope string_scope.


Context (Name Tyname BinderName BinderTyname : Set).

Definition Kind := kind.
Definition Ty := ty Tyname BinderTyname.
Definition Term := term Name Tyname BinderName BinderTyname.
Definition Binding := binding Name Tyname BinderName BinderTyname.
Notation VDecl := (vdecl Name Tyname BinderName).
Notation TVDecl := (tvdecl BinderTyname).
Notation DTDecl := (dtdecl Name Tyname BinderTyname).
Notation constructor := (constr Tyname BinderName BinderTyname).

(* Typing/kinding contexts *)
Context (Context : Set) 
        (empty : Context)
        (lookupT : Context -> Name -> option Ty)
        (lookupK : Context -> Tyname -> option Kind) 
        (extendT : BinderName -> Ty -> Context -> Context)
        (extendK : BinderTyname -> Kind -> Context -> Context).
Context (flatten : list Context -> Context)
        (append : Context -> Context -> Context)
        (binds : Binding -> Context)
        (fromDecl : TVDecl -> Context).

(* Builtins *)
Context (lookupBuiltinTy : DefaultFun -> Ty). 
Context (substituteT : BinderTyname -> Ty -> Ty -> Ty).
Context (listOfArgumentTypes : Ty -> list Ty).

Context (unwrapIFix : Ty -> BinderTyname -> Kind -> Ty -> Ty).

(** ** Kinding of types *)
Reserved Notation "ctx '|-*' ty ':' K" (at level 40, ty at level 0, K at level 0).
Inductive has_kind : Context -> Ty -> Kind -> Prop :=
  | K_Var : forall ctx X K,
      lookupK ctx X = Coq.Init.Datatypes.Some K ->
      ctx |-* (Ty_Var X) : K
  | K_Fun : forall ctx T1 T2,
      ctx |-* T1 : Kind_Base ->
      ctx |-* T2 : Kind_Base ->
      ctx |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall ctx F T K,
      ctx |-* T : K ->
      ctx |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      ctx |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall ctx X K T,
      (extendK X K ctx) |-* T : Kind_Base ->
      ctx |-* (Ty_Forall X K T) : Kind_Base
  (* Note on builtins: At the moment of writing this, all built-in types are of base kind. *)
  | K_Builtin : forall ctx u,
      ctx |-* (Ty_Builtin u) : Kind_Base 
  | K_Lam : forall ctx X K1 T K2,
      (extendK X K1 ctx) |-* T : K2 ->
      ctx |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall ctx T1 T2 K1 K2,
      ctx |-* T1 : (Kind_Arrow K1 K2) ->
      ctx |-* T2 : K1 ->
      ctx |-* (Ty_App T1 T2) : K2
where "ctx '|-*' ty ':' K" := (has_kind ctx ty K).


(** ** Type equality (beta-reduction) *)
(* TODO: Alpha-equivalence*)
Reserved Notation "T1 '=b' T2" (at level 40).
Inductive EqT : Ty -> Ty -> Prop :=
  (* Beta-reduction *)
  | Q_Beta : forall X K T1 T2,
      Ty_App (Ty_Lam X K T1) T2 =b substituteT X T2 T1
  (* Reflexivity, Symmetry and Transitivity*)
  | Q_Refl : forall T,
      T =b T
  | Q_Symm : forall T S,
      T =b S ->
      S =b T
  | Q_Trans : forall S U T,
      S =b U ->
      U =b T ->
      S =b T
  (* Congruence *)
  | Q_Fun : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_Fun S1 T1 =b Ty_Fun S2 T2
  | Q_Forall : forall X K S T,
      S =b T ->
      Ty_Forall X K S =b Ty_Forall X K T
  | Q_Lam : forall X K S T,
      S =b T ->
      Ty_Lam X K S =b Ty_Lam X K T
  | Q_App : forall S1 S2 T1 T2,
      S1 =b S2 ->
      T1 =b T2 ->
      Ty_App S1 T1 =b Ty_App S2 T2
where "T1 '=b' T2" := (EqT T1 T2).

(** ** Typing of terms *)
Reserved Notation "ctx '|-+' tm ':' T" (at level 40, tm at level 0, T at level 0).
Inductive has_type : Context -> Term -> Ty -> Prop :=
  (* Let-bindings *)
  | T_Let : forall ctx bs t T,
      ctx |-* T : Kind_Base ->
      (forall b, In b bs -> binding_well_formed ctx b) ->
      (append (flatten (map binds bs)) ctx) |-+ t : T ->
      ctx |-+ (Let NonRec bs t) : T
  | T_LetRec : forall ctx bs t T ctx',
      ctx |-* T : Kind_Base ->
      ctx' = append (flatten (map binds bs)) ctx ->
      (forall b, In b bs -> binding_well_formed ctx' b) ->
      ctx' |-+ t : T ->
      ctx |-+ (Let Rec bs t) : T
  (* Basic constructs *)
  | T_Var : forall ctx x T,
      lookupT ctx x = Coq.Init.Datatypes.Some T ->
      ctx |-+ (Var x) : T
  | T_TyAbs : forall ctx X K t T,
      (extendK X K ctx) |-+ t : T ->
      ctx |-+ (TyAbs X K t) : (Ty_Forall X K T)
  | T_LamAbs : forall ctx x T1 t T2,
      (extendT x T1 ctx) |-+ t : T2 -> 
      ctx |-* T1 : Kind_Base ->
      ctx |-+ (LamAbs x T1 t) : (Ty_Fun T1 T2)
  | T_Apply : forall ctx t1 t2 T1 T2,
      ctx |-+ t1 : (Ty_Fun T1 T2) ->
      ctx |-+ t2 : T1 ->
      ctx |-+ (Apply t1 t2) : T2
  | T_Constant : forall ctx u type,
      ctx |-+ (Constant (Some (ValueOf u type))) : (Ty_Builtin (Some (TypeIn u))) (* TODO *)
  | T_Builtin : forall ctx f,
      ctx |-+ (Builtin f) : (lookupBuiltinTy f)
  | T_TyInst : forall ctx t1 T2 T1 X K2,
      ctx |-+ t1 : (Ty_Forall X K2 T1) ->
      ctx |-* T2 : K2 ->
      ctx |-+ (TyInst t1 T2) : (substituteT X T2 T1)
  | T_Error : forall ctx T,
      ctx |-* T : Kind_Base ->
      ctx |-+ (Error T) : T 
  (* Recursive types *)
  | T_IWrap : forall ctx F T M X K,
      ctx |-+ M : (unwrapIFix F X K T) ->
      ctx |-* T : K ->
      ctx |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      ctx |-+ (IWrap F T M) : (Ty_IFix F T)
  | T_Unwrap : forall ctx M F X K T,
      ctx |-+ M : (Ty_IFix F T) ->
      ctx |-* T : K ->
      ctx |-+ (Unwrap M) : (unwrapIFix F X K T)
  (* Type equality *)
  | T_Eq : forall ctx t T S,
      ctx |-+ t : S ->
      S =b T ->
      ctx |-+ t : T

  with constructor_well_formed : Context -> constructor -> Prop :=
    | W_Con : forall ctx x T ar,
        (forall U, In U (listOfArgumentTypes T) -> ctx |-* U : Kind_Base) ->
        constructor_well_formed ctx (Constructor (VarDecl x T) ar)
  
  with binding_well_formed : Context -> Binding -> Prop :=
    | W_Term : forall ctx s x T t,
        ctx |-* T : Kind_Base ->
        ctx |-+ t : T ->
        binding_well_formed ctx (TermBind s (VarDecl x T) t)
    | W_Type : forall ctx X K T,
        ctx |-* T : K ->
        binding_well_formed ctx (TypeBind (TyVarDecl X K) T)
    | W_Data : forall ctx X YKs cs matchFunc ctx',
        ctx' = append (flatten (map fromDecl YKs)) ctx ->
        (forall c, In c cs -> constructor_well_formed ctx' c) ->
        binding_well_formed ctx (DatatypeBind (Datatype X YKs matchFunc cs))

  where "ctx '|-+' tm ':' T" := (has_type ctx tm T).

End Typing.
