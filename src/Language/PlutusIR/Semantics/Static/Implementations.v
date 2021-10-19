Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.
Require Export PlutusCert.Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.
Require Export PlutusCert.Util.Map.
Require Export PlutusCert.Util.Map.Mupdate.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.
Require Export PlutusCert.Language.PlutusIR.Semantics.Static.TypeSubstitution.CaptureAvoiding.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(** ** Contexts and lookups *)
Definition Delta : Type := partial_map Kind.
Definition Gamma : Type := partial_map Ty.

Definition flatten {A : Type} (l : list (list A)) := List.concat (rev l).

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
    rev (map (constrBind d) cs)
  end.

Definition matchBind (d : DTDecl) : name * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
    (matchFunc, matchTy d)
  end.

Import ListNotations.
Open Scope list_scope.
(*
Definition binds (b : Binding) : list (name * Ty) * list (tyname * Kind) :=
  match b with
  | TermBind _ vd _ => ((getName vd, getTy vd) :: nil, nil)
  | TypeBind tvd ty => (nil, (getTyname tvd, getKind tvd) :: nil)
  | DatatypeBind d =>
    let dataB := dataBind d in 
    let constrBs := constrBinds d in
    let constrBs_ctx : Context := fold_right append emptyContext (map (fun x => (fst x |T-> snd x ; emptyContext)) constrBs) in
    let matchB := matchBind d in
    (fst matchB |T-> snd matchB ; (append constrBs_ctx (fst dataB |K-> snd dataB ; emptyContext)))
  end.
*)

Definition binds_Delta (b : Binding) : list (tyname * Kind) :=
  match b with
  | TermBind _ _ _ => nil
  | TypeBind (TyVarDecl X K) ty => (X, K) :: nil
  | DatatypeBind d => dataBind d :: nil
  end.

Definition binds_Gamma (b : Binding) : list (name * Ty) :=
  match b with
  | TermBind _ (VarDecl x T) _ => (x, T) :: nil
  | TypeBind _ _ => nil 
  | DatatypeBind d => 
      let constrBs := constrBinds d in
      let matchB := matchBind d in
      matchB :: constrBs
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
Fixpoint splitTy (T : Ty) : list Ty * Ty :=
  match T with
  | Ty_Fun Targ T' => (cons Targ (fst (splitTy T')), snd (splitTy T'))
  | Tr => (nil, Tr)
  end.

Definition combineTy (Targs : list Ty) (Tr : Ty) : Ty :=
  fold_right (@Ty_Fun tyname binderTyname) Tr Targs.

Definition fromDecl (tvd : tvdecl tyname) : tyname * Kind :=
  match tvd with
  | TyVarDecl v K => (v, K)   
  end.
    
Definition unwrapIFix (F : Ty) (K : Kind) (T : Ty) : Ty := (Ty_App (Ty_App F (Ty_Lam "X" K (Ty_IFix F (Ty_Var "X")))) T).


(*
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
  | Ty_IFix F T => Ty_IFix (beta_reduce F) (beta_reduce T)
  | Ty_Builtin st => Ty_Builtin st
  end.
*)