Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import Util.
Import NamedTerm.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** Getters *)
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

(** Auxiliary functions *)

(*  Applies a type to multiple arguments 
      Ty_Apps f [x_1; ... ; x_n] = ((f x_1) ... ) x_n
*)
Definition Ty_Apps (f : Ty) (xs : list Ty) : Ty :=
  fold_left Ty_App xs f
.

(* Polymorphic type over multiple type parameters
     Ty_Foralls [x_1; ... ; x_n] t = ∀ x_1 ... ∀ x_n . t
*)
Definition Ty_Foralls (xs : list TVDecl) (t : Ty) : Ty :=
  fold_right (fun YK t' => Ty_Forall (getTyname YK) (getKind YK) t') t xs
.

(* Type lambda over multiple parameters
 *)
Definition Ty_Lams (xs : list TVDecl) (t : Ty) : Ty :=
  fold_right (fun YK t' => Ty_Lam (getTyname YK) (getKind YK) t') t xs
.

(* Type of a branch in a match. The result type of the constructor is replaced
 * by some result type.
 *)
Definition branchTy (c : VDecl) (R : Ty) : Ty :=
  match c with
  | VarDecl x T =>
    let
      fix branchTy' S :=
        match S with
        | Ty_Fun S1 S2 => Ty_Fun S1 (branchTy' S2)
        | _ => R
        end
    in
      branchTy' T
  end.

Definition dataTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let branchTypes : list Ty := map (fun c => branchTy c (Ty_Var "R")) cs in
      let branchTypesFolded := fold_right Ty_Fun (Ty_Var "R") branchTypes in
      Ty_Lams YKs (Ty_Forall "R" Kind_Base branchTypesFolded)
  end.


(* The expected return type of a constructor, i.e. the Datatype applied to all
 * its type parameters. For example: Either a b
 *)
Definition constrLastTyExpected (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let tyParamVars := map (Ty_Var ∘ getTyname) YKs in
      Ty_Apps (Ty_Var (getTyname X)) tyParamVars
  end.


(* The type of a constructor is not just its annotation,
 * it requires Ty_Forall for all of the datatype's type parameters
 *)
Definition constrTy (d : DTDecl) (c : VDecl) : Ty :=
  match d, c with
  | Datatype _ YKs _ _, VarDecl _ T =>
      Ty_Foralls YKs T
  end.

Definition matchTy (d : DTDecl) : Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let tyParamVars := map (Ty_Var ∘ getTyname) YKs in
      Ty_Foralls YKs (Ty_Fun (constrLastTyExpected d) (Ty_Apps (dataTy d) tyParamVars))
  end.

(** Binder functions *)
Definition constrBind (d : DTDecl) (c : VDecl) : string * Ty :=
  match c with
  | VarDecl x _ =>
      (x, constrTy d c)
  end.

Definition constrBinds (d : DTDecl) : list (string * Ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
      rev (map (constrBind d) cs)
  end.

Definition matchBind (d : DTDecl) : string * Ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      (matchFunc, matchTy d)
  end.

Definition binds_Delta (b : Binding) : list (string * Kind) :=
  match b with
  | TermBind _ _ _ => nil
  | TypeBind (TyVarDecl X K) ty => (X, K) :: nil
  | DatatypeBind (Datatype (TyVarDecl X K) _ _ _) => (X, K):: nil
  end.

Definition binds_Gamma (b : Binding) : list (string * Ty) :=
  match b with
  | TermBind _ (VarDecl x T) _ => (x, T) :: nil
  | TypeBind _ _ => nil
  | DatatypeBind d =>
      let constrBs := constrBinds d in
      let matchB := matchBind d in
      matchB :: constrBs
  end.
