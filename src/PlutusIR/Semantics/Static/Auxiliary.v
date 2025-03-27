Require Import PlutusCert.PlutusIR.
From PlutusCert Require Import Util.
From PlutusCert Require Import FreeVars.

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

(* Replace the return type of T with R, e.g.
   replaceRetTy (A -> B) C = A -> B -> C
*)
Fixpoint replaceRetTy (T R : ty) : ty :=
  match T with
   | Ty_Fun S1 S2 => Ty_Fun S1 (replaceRetTy S2 R)
   | _ => R
  end.

Example replaceRetTy_bin A B C :
  replaceRetTy (Ty_Fun (Ty_Var A) (Ty_Var B)) (Ty_Var C) = Ty_Fun (Ty_Var A) (Ty_Var C).
Proof. reflexivity. Qed.


(* Used as binder in the type of matchTy *)
Definition dtdecl_freshR (d : dtdecl) : string :=
  match d with
  | Datatype XK YKs matchFunc cs =>
      concat ""
        (List.concat (map (fun c => Ty.ftv (vdecl_ty c)) cs))
  end
.

(* The expected return type of a constructor, i.e. the Datatype applied to all
 * its type parameters. For example: Either a b
 *)
Definition constrLastTyExpected dtd : ty :=
  match dtd with
  | Datatype XK YKs _ _ =>
      let X := tvdecl_name XK in
      let Ys := map tvdecl_name YKs in
      Ty_Apps (Ty_Var X) (map Ty_Var Ys)
  end.

(* The type of match function, in the case of
     data Either a b = Left : a -> Either a b | Right : b -> Either a b
   the match function will have type
     ∀a b. Either a b -> ∀R. (a -> R) -> (b -> R) -> R
*)
Definition matchTy (d : dtdecl) : ty :=
  let R := dtdecl_freshR d in
  match d with
  | Datatype X YKs matchFunc cs =>
      let branchTypes := map (fun c => replaceRetTy (vdecl_ty c) (Ty_Var R)) cs in
      let branchTypesFolded := fold_right Ty_Fun (Ty_Var R) branchTypes in
      Ty_Foralls YKs
        (Ty_Fun (constrLastTyExpected d)
          (Ty_Forall R Kind_Base branchTypesFolded)
        )
  end.



(* The type of a constructor is not just its annotation,
 * it requires Ty_Forall for all of the datatype's type parameters
 *)
Definition constrTy (d : dtdecl) (c : vdecl) : ty :=
  match d, c with
  | Datatype _ YKs _ _, VarDecl _ T =>
      Ty_Foralls YKs T
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

Section EXAMPLE_EITHER.

Local Open Scope string_scope.


Notation "X '→' Y" := (Ty_Fun X Y) (at level 49, right associativity).

Definition either_kind := Kind_Arrow Kind_Base (Kind_Arrow Kind_Base Kind_Base).
Definition either_applied := Ty_App (Ty_App (Ty_Var "Either") (Ty_Var "a")) (Ty_Var "b").

Definition dtd_either :=
  Datatype
    (TyVarDecl "Either" either_kind)
    [ TyVarDecl "a" Kind_Base
    ; TyVarDecl "b" Kind_Base
    ]
    "matchEither"
    [ VarDecl "Left" (Ty_Fun (Ty_Var "a") (either_applied))
    ; VarDecl "Right" (Ty_Fun (Ty_Var "b") (either_applied))
    ]
.

Compute (matchTy dtd_either).

Example either_matchTy : matchTy dtd_either =
  Ty_Forall "a" Kind_Base
    (Ty_Forall "b" Kind_Base
       (Ty_App (Ty_App (Ty_Var "Either") (Ty_Var "a")) (Ty_Var "b")
        → Ty_Forall "aEitherabbEitherab" Kind_Base
            ((Ty_Var "a" → Ty_Var "aEitherabbEitherab")
             → (Ty_Var "b" → Ty_Var "aEitherabbEitherab")
               → Ty_Var "aEitherabbEitherab")))
               .
Proof. reflexivity. Qed.

End EXAMPLE_EITHER.
