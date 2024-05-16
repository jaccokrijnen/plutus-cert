Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import Util.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(** Getters *)
Definition getName (vd : vdecl) :=
  match vd with
  | VarDecl x _ => x
  end.

Definition getTy (vd : vdecl) :=
  match vd with
  | VarDecl _ T => T
  end.

Definition getTyname (tvd : tvdecl) :=
  match tvd with
  | TyVarDecl X _ => X
  end.

Definition getKind (tvd : tvdecl) :=
  match tvd with
  | TyVarDecl _ K => K
  end.

(** Auxiliary functions *)

(*  Applies a type to multiple arguments 
      Ty_Apps f [x_1; ... ; x_n] = ((f x_1) ... ) x_n
*)
Definition Ty_Apps (f : ty) (xs : list ty) : ty :=
  fold_left Ty_App xs f
.

(* Polymorphic type over multiple type parameters
     Ty_Foralls [x_1; ... ; x_n] t = ∀ x_1 ... ∀ x_n . t
*)
Definition Ty_Foralls (xs : list tvdecl) (t : ty) : ty :=
  fold_right (fun YK t' => Ty_Forall (getTyname YK) (getKind YK) t') t xs
.

(* Type lambda over multiple parameters
 *)
Definition Ty_Lams (xs : list tvdecl) (t : ty) : ty :=
  fold_right (fun YK t' => Ty_Lam (getTyname YK) (getKind YK) t') t xs
.

(* Type of a branch in a match. The result type of the constructor is replaced
 * by some result type.
 *)
Definition branchTy (c : vdecl) (R : ty) : ty :=
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

Definition dataTy (d : dtdecl) : ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let branchTypes : list ty := map (fun c => branchTy c (Ty_Var "R")) cs in
      let branchTypesFolded := fold_right Ty_Fun (Ty_Var "R") branchTypes in
      Ty_Lams YKs (Ty_Forall "R" Kind_Base branchTypesFolded)
  end.


(* The expected return type of a constructor, i.e. the Datatype applied to all
 * its type parameters. For example: Either a b
 *)
Definition constrLastTyExpected (d : dtdecl) : ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let tyParamVars := map (Ty_Var ∘ getTyname) YKs in
      Ty_Apps (Ty_Var (getTyname X)) tyParamVars
  end.


(* The type of a constructor is not just its annotation,
 * it requires Ty_Forall for all of the datatype's type parameters
 *)
Definition constrTy (d : dtdecl) (c : vdecl) : ty :=
  match d, c with
  | Datatype _ YKs _ _, VarDecl _ T =>
      Ty_Foralls YKs T
  end.

Definition matchTy (d : dtdecl) : ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      let tyParamVars := map (Ty_Var ∘ getTyname) YKs in
      Ty_Foralls YKs (Ty_Fun (constrLastTyExpected d) (Ty_Apps (dataTy d) tyParamVars))
  end.

(** Binder functions *)
Definition constrBind (d : dtdecl) (c : vdecl) : string * ty :=
  match c with
  | VarDecl x _ =>
      (x, constrTy d c)
  end.

Definition constrBinds (d : dtdecl) : list (string * ty) :=
  match d with
  | Datatype X YKs matchFunc cs =>
      rev (map (constrBind d) cs)
  end.

Definition matchBind (d : dtdecl) : string * ty :=
  match d with
  | Datatype X YKs matchFunc cs =>
      (matchFunc, matchTy d)
  end.

Definition binds_Delta (b : binding) : list (string * kind) :=
  match b with
  | TermBind _ _ _ => nil
  | TypeBind (TyVarDecl X K) ty => (X, K) :: nil
  | DatatypeBind (Datatype (TyVarDecl X K) _ _ _) => (X, K):: nil
  end.

Definition binds_Gamma (b : binding) : list (string * ty) :=
  match b with
  | TermBind _ (VarDecl x T) _ => (x, T) :: nil
  | TypeBind _ _ => nil
  | DatatypeBind d =>
      let constrBs := constrBinds d in
      let matchB := matchBind d in
      matchB :: constrBs
  end.
