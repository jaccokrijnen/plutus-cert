Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Map.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Local Open Scope string_scope.

(** ** Contexts and lookups *)
Definition Delta : Type := partial_map Kind.
Definition Gamma : Type := partial_map Ty.
Definition Context : Type := Delta * Gamma.

Definition emptyContext : Context := (Map.empty, Map.empty).

Definition lookupK (ctx : Context) (X : tyname) : option Kind :=
  fst ctx X.
Definition lookupT (ctx : Context) (x : name) : option Ty :=
  snd ctx x.

Definition extendK X K ctx : Context := (X |-> K; fst ctx, snd ctx).
Definition extendT x T ctx : Context := (fst ctx, x |-> T ; snd ctx).

Notation "x '|T->' T ';' ctx" := (extendT x T ctx) (at level 60, right associativity).
Notation "X '|K->' K ';' ctx" := (extendK X K ctx) (at level 60, right associativity).

Lemma cong_eq : forall {A B} (x1 x2 : A) (y1 y2 : B), x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof. intros. f_equal; auto. Qed. 

Lemma lookupT_eq : forall ctx x T,
    lookupT (x |T-> T ; ctx) x = Datatypes.Some T.
Proof. intros. unfold lookupT. simpl. rewrite update_eq. reflexivity. Qed.

Lemma lookupK_eq : forall ctx X K,
    lookupK (X |K-> K ; ctx) X = Datatypes.Some K.
Proof. intros. unfold lookupK. simpl. rewrite update_eq. reflexivity. Qed.

Lemma lookupT_neq : forall ctx x1 x2 T,
    x2 <> x1->
    lookupT (x2 |T-> T ; ctx) x1 = lookupT ctx x1.
Proof. intros. unfold lookupT. simpl. rewrite update_neq. reflexivity. assumption. Qed.

Lemma lookupK_neq : forall ctx X1 X2 K,
    X2 <> X1 ->
    lookupK (X2 |K-> K ; ctx) X1 = lookupK ctx X1.
Proof. intros. unfold lookupT. simpl. rewrite update_neq. reflexivity. assumption. Qed.

Lemma lookupT_extendK : forall ctx X K x,
  lookupT (X |K-> K; ctx) x = lookupT ctx x.
Proof. reflexivity. Qed.

Lemma lookupK_extendT : forall ctx x T X,
  lookupK (x |T-> T; ctx) X = lookupK ctx X.
Proof. reflexivity. Qed.

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
    (fun X =>
      match lookupK ctx1 X with
      | Coq.Init.Datatypes.Some K => Coq.Init.Datatypes.Some K
      | None => lookupK ctx2 X
      end)
    (fun x =>
      match lookupT ctx1 x with
      | Coq.Init.Datatypes.Some T => Coq.Init.Datatypes.Some T
      | None => lookupT ctx2 x
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
    destruct (d x); auto.
  - apply functional_extensionality.
    intros.
    destruct (g x); auto.
Qed.

Lemma append_singleton_l : forall x T ctx,
    append (x |T-> T ; emptyContext) ctx = (x |T-> T ; ctx).
Proof. 
  intros. unfold append. simpl. destruct ctx. unfold extendT. simpl. 
  apply cong_eq.
  - reflexivity.
  - apply functional_extensionality.
    intros.
    unfold update.
    unfold t_update.
    destruct (x =? x0); auto.
Qed.

Lemma lookupT_append_r : forall ctx ctx' ctx'' x,
    lookupT ctx' x = lookupT ctx'' x ->
    lookupT (append ctx ctx') x = lookupT (append ctx ctx'') x.
Proof. intros. destruct ctx. simpl. destruct (g x); auto. Qed.

Lemma lookupK_append_r : forall ctx ctx' ctx'' X,
    lookupK ctx' X = lookupK ctx'' X ->
    lookupK (append ctx ctx') X = lookupK (append ctx ctx'') X.
Proof. intros. destruct ctx. simpl. destruct (d X); auto. Qed.

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
    destruct (d x); auto.
  - simpl.
    apply functional_extensionality.
    intros.
    destruct (g x); auto.
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

Lemma flatten_extract : forall ctx ctxs,
    flatten (ctx :: ctxs) = append (flatten ctxs) ctx.
Proof.
  intros.
  unfold flatten.
  simpl.
  replace ctx with (concat (ctx :: nil)) by eauto using append_emptyContext_r.
  rewrite concat_append.
  simpl.
  rewrite append_emptyContext_r.
  reflexivity.
Qed.



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

Definition fromDecl (tvd : tvdecl tyname) : Context :=
  match tvd with
  | TyVarDecl v K => extendK v K emptyContext
  end.
    
Definition unwrapIFix (F : Ty) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).

Fixpoint beta_reduce (T : Ty) : Ty :=
  match T with
  (* Beta-reduction *)
  | Ty_App T1 T2 => 
    match beta_reduce T1, beta_reduce T2 with
    | Ty_Lam X K T1', T2' => substituteT X T2' T1'
    | T1', T2' => Ty_App T1' T2'
    end
  | Ty_Fun T1 T2 => Ty_Fun (beta_reduce T1) (beta_reduce T2)
  | Ty_Forall X K T0 => Ty_Forall X K (beta_reduce T0)
  | Ty_Lam X K T0 => Ty_Lam X K (beta_reduce T0)
  | Ty_Var X => Ty_Var X
  | Ty_IFix F T => Ty_IFix F T
  | Ty_Builtin st => Ty_Builtin st
  end.