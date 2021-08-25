Require Import PlutusCert.Language.PlutusIR.Semantics.Static.
Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Map.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Local Open Scope string_scope.

(** ** Contexts and lookups *)
Definition Context : Type := partial_map Ty * partial_map Kind.

Definition emptyContext : Context := (Map.empty, Map.empty).

Definition lookupT (ctx : Context) (x : name) : option Ty :=
  fst ctx x.

Definition lookupK (ctx : Context) (X : tyname) : option Kind :=
  snd ctx X.

Definition extendT x T ctx : Context := ((x |-> T ; fst ctx), snd ctx).
Definition extendK X K ctx : Context := (fst ctx, (X |-> K; snd ctx)).

Notation "x '|T->' T ';' ctx" := (extendT x T ctx) (at level 60, right associativity).
Notation "X '|K->' K ';' ctx" := (extendK X K ctx) (at level 60, right associativity).

Lemma cong_eq : forall {A B} (x1 x2 : A) (y1 y2 : B), x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof. intros. f_equal; auto. Qed. 

Lemma extendT_shadow : forall ctx x T1 T2,
    (x |T-> T1; x |T-> T2; ctx) = (x |T-> T1; ctx).
Proof. 
  intros. destruct ctx. unfold extendT. simpl. 
  f_equal.
  apply update_shadow.
Qed.

Lemma extendT_permute : forall ctx x1 x2 T1 T2,
    x2 <> x1 ->
    (x1 |T-> T1 ; x2 |T-> T2 ; ctx) = (x2 |T-> T2 ; x1 |T-> T1 ; ctx).
Proof.
  intros. destruct ctx. unfold extendT. simpl. f_equal. apply update_permute. assumption. Qed.

Lemma extendT_extendK_permute : forall x T Y K ctx,
    (Y |K-> K ; x |T-> T ; ctx) = (x |T-> T ; Y |K-> K ; ctx).
Proof.
  intros.
  destruct ctx.
  unfold extendT.
  unfold extendK.
  simpl.
  apply cong_eq; auto.
Qed.

Definition append ctx1 ctx2 : Context := 
  pair
    (fun x =>
      match lookupT ctx1 x with
      | Coq.Init.Datatypes.Some T => Coq.Init.Datatypes.Some T
      | None => lookupT ctx2 x
      end)
    (fun X =>
      match lookupK ctx1 X with
      | Coq.Init.Datatypes.Some K => Coq.Init.Datatypes.Some K
      | None => lookupK ctx2 X
      end).
Definition concat ctxs : Context := List.fold_right append emptyContext ctxs.
Definition flatten ctxs : Context := concat (rev ctxs).

Lemma append_emptyContext_l : forall ctx,
    append emptyContext ctx = ctx.
Proof. intros. destruct ctx. reflexivity. Qed.

Lemma append_emptyContext_r : forall ctx,
    append ctx emptyContext = ctx.
Proof. 
  intros. destruct ctx. unfold append. simpl.
  apply cong_eq.
  - apply functional_extensionality.
    intros.
    destruct (p x); auto.
  - apply functional_extensionality.
    intros.
    destruct (p0 x); auto.
Qed.

Lemma append_singleton_l : forall x T ctx,
    append (x |T-> T ; emptyContext) ctx = (x |T-> T ; ctx).
Proof. 
  intros. unfold append. simpl. destruct ctx. unfold extendT. simpl. 
  apply cong_eq.
  - apply functional_extensionality.
    intros.
    unfold update.
    unfold t_update.
    destruct (x =? x0); auto.
  - reflexivity.
Qed.

Lemma append_assoc : forall ctx1 ctx2 ctx3,
    append ctx1 (append ctx2 ctx3) = append (append ctx1 ctx2) ctx3.
Proof.
  intros.
  destruct ctx1.
  destruct ctx2.
  destruct ctx3.
  unfold append.
  f_equal.
  - simpl.
    apply functional_extensionality.
    intros.
    destruct (p x); auto.
  - simpl.
    apply functional_extensionality.
    intros.
    destruct (p0 x); auto.
Qed.

Lemma concat_append : forall ctx1 ctx2,
    concat (ctx1 ++ ctx2) = append (concat ctx1) (concat ctx2).
Proof. 
  induction ctx1.
  - intros.
    simpl.
    rewrite append_emptyContext_l.
    reflexivity.
  - intros.
    simpl.
    rewrite <- append_assoc.
    f_equal.
    apply IHctx1.
Qed.

Lemma flatten_nil : flatten nil = emptyContext.
Proof. reflexivity. Qed.

Definition constructorDecl : constructor -> VDecl :=
  fun c => match c with
  | Constructor vd _ => vd
  end.

(** *** Auxiliary functions *)
Definition getName (vd : VDecl) :=
  match vd with
  | VarDecl x _ => x
  end.

Definition getTy (vd : VDecl) :=
  match vd with
  | VarDecl _ T => T
  end.

Definition getTyname (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl X _ => X
  end.

Definition getKind (tvd : TVDecl) :=
  match tvd with
  | TyVarDecl _ K => K
  end.

Definition getMatchFunc (d : DTDecl) :=
  match d with
  | Datatype _ _ matchFunc _ => matchFunc
  end.

Definition branchTy (c : constructor) (R : Ty) : Ty :=
  match c with
  | Constructor (VarDecl x T) _ => 
    match T with
    | Ty_Fun T1 T2 => Ty_Fun T1 R
    | _ => R
    end
  end.

Open Scope string_scope.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let branchTypes : list Ty := map (fun c => branchTy c (Ty_Var "R")) cs in
    let branchTypesFolded := fold_right (@Ty_Fun tyname binderTyname) (Ty_Var "R") branchTypes in
    let indexKinds := map (fun YK => Ty_Lam (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Forall "R" Kind_Base branchTypesFolded) indexKinds
  end.

Definition dataKind (d : DTDecl) : Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    fold_right Kind_Arrow Kind_Base (map getKind YKs)
  end.

Definition constrTy (d : DTDecl) (c : constructor) : Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    let indexTyVars := map (compose (@Ty_Var tyname binderTyname) getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left (@Ty_App tyname binderTyname) indexTyVars (Ty_Var (getTyname X)) in
    let branchType := branchTy c indexTyVarsAppliedToX in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply branchType indexForalls
  end.

Definition matchTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    let indexTyVars := map (compose (@Ty_Var tyname binderTyname) getTyname) YKs in
    let indexTyVarsAppliedToX := fold_left (@Ty_App tyname binderTyname) indexTyVars (Ty_Var (getTyname X)) in
    let indexForalls := map (fun YK => Ty_Forall (getTyname YK) (getKind YK)) YKs in
    fold_right apply (Ty_Fun indexTyVarsAppliedToX (fold_left (@Ty_App tyname binderTyname) indexTyVars (dataTy d))) indexForalls 
  end.

(** *** Binder functions *)
Definition dataBind (d : DTDecl) : tyname * Kind :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (getTyname X, dataKind d)
  end.

Definition constrBind (d : DTDecl) (c : constructor) : name * Ty :=
  match d, c with
  | Datatype X YKs matchFunc cs, Constructor (VarDecl x T) _ =>
    (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (name * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
    map (constrBind d) cs
  end.

Definition matchBind (d : DTDecl) : name * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (matchFunc, matchTy d)
  end.

Import ListNotations.
Open Scope list_scope.

Definition binds (b : Binding) : Context :=
  match b with
  | TermBind _ vd _ => (getName vd |T-> getTy vd ; emptyContext)
  | TypeBind tvd ty => (getTyname tvd |K-> getKind tvd ; emptyContext)
  | DatatypeBind d =>
    let dataB := dataBind d in 
    let constrBs := constrBinds d in
    let constrBs_ctx : Context := fold_right append emptyContext (map (fun x => (fst x |T-> snd x ; emptyContext)) constrBs) in
    let matchB := matchBind d in
    (fst matchB |T-> snd matchB ; (append constrBs_ctx (fst dataB |K-> snd dataB ; emptyContext)))
  end.

(** ** Kinds of builtin types *)
Definition lookupBuiltinKind (u : DefaultUni) : Kind := 
  match u with
  | DefaultUniInteger    => Kind_Base
  | DefaultUniByteString => Kind_Base
  | DefaultUniString     => Kind_Base
  | DefaultUniChar       => Kind_Base
  | DefaultUniUnit       => Kind_Base
  | DefaultUniBool       => Kind_Base
  end.

(** ** Types of builtin functions *)
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

(** ** Well-formedness of constructors and bindings *)
Fixpoint listOfArgumentTypes (T : Ty) : list Ty :=
  match T with
  | Ty_Fun T1 T2 => cons T1 (listOfArgumentTypes T2)
  | _ => nil
  end.

(** ** Substitution in types *)
Fixpoint substituteT (X : tyname) (S T : Ty) : Ty :=
  match T with
  | Ty_Var Y => 
    if X =? Y then S else Ty_Var Y
  | Ty_Fun T1 T2 =>
    Ty_Fun (substituteT X S T1) (substituteT X S T2)
  | Ty_IFix F T =>
    Ty_IFix (substituteT X S F) (substituteT X S T)
  | Ty_Forall Y K T' =>
    if X =? Y then Ty_Forall Y K T' else Ty_Forall Y K (substituteT X S T')
  | Ty_Builtin u => 
    Ty_Builtin u
  | Ty_Lam Y K1 T' =>
    if X =? Y then Ty_Lam Y K1 T' else Ty_Lam Y K1 (substituteT X S T')
  | Ty_App T1 T2 =>
    Ty_App (substituteT X S T1) (substituteT X S T2)
  end.

Definition fromDecl (tvd : tvdecl tyname) : Context :=
  match tvd with
  | TyVarDecl v K => extendK v K emptyContext
  end.
    
Definition unwrapIFix (F : Ty) (X : binderTyname) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam X K (Ty_IFix F (Ty_Var X)))) T).

Definition has_kind__named : Context -> Ty -> Kind -> Prop := has_kind tyname binderTyname Context lookupK extendK lookupBuiltinKind.

Notation "ctx '|-*' T ':' K" := (has_kind tyname binderTyname Context lookupK extendK lookupBuiltinKind ctx T K) (at level 40, T at level 0, K at level 0).

Definition has_type__named : Context -> Term -> Ty -> Prop := has_type name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix.

Notation "ctx '|-+' tm ':' T" := (has_type name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix ctx tm T) (at level 40, tm at level 0, T at level 0).

Definition EqT__named : Ty -> Ty -> Prop := EqT tyname binderTyname substituteT.

Notation "T1 '=b' T2" := (EqT tyname binderTyname substituteT T1 T2) (at level 40).

Definition constructor_well_formed__named : Context -> constructor -> Prop := constructor_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix.

Notation "ctx '|-ok_c' c" := (constructor_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix ctx c) (at level 40, c at level 0).

Definition bindings_well_formed_nonrec__named : Context -> list Binding -> Prop := bindings_well_formed_nonrec name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix.

Notation "ctx '|-oks_nr' bs" := (bindings_well_formed_nonrec name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix ctx bs) (at level 40, bs at level 0).

Definition bindings_well_formed_rec__named : Context -> list Binding -> Prop := bindings_well_formed_rec name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix.

Notation "ctx '|-oks_r' bs" := (bindings_well_formed_rec name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix ctx bs) (at level 40, bs at level 0).

Definition binding_well_formed__named : Context -> Binding -> Prop := binding_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix.

Notation "ctx '|-ok' tm" := (binding_well_formed name tyname binderName binderTyname Context lookupT lookupK extendT extendK flatten append binds fromDecl lookupBuiltinKind lookupBuiltinTy substituteT listOfArgumentTypes unwrapIFix ctx tm) (at level 40, tm at level 0).