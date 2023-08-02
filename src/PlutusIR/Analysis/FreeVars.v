Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import
  PlutusIR
  PlutusIR.Folds
  Analysis.BoundVars
  Util
.


Section ListHelpers.

  (* Todo: use Lists.List.remove and EqDec instances *)

  Context
    {A : Set}
    (A_eqb : A -> A -> bool)
    .

  Definition delete : A -> list A -> list A :=
    fun x xs => filter (fun y => negb (A_eqb x y)) xs.

  Definition elem x xs := existsb (A_eqb x) xs.

  Definition delete_many : list A -> list A -> list A :=
    fun ds xs => filter (fun x => negb (elem x ds)) xs.

End ListHelpers.

(* Parametrized for _named_ binders (not de Bruijn) *)
Section FreeVars.

  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    (tyvar_eqb : var -> var -> bool)
    .

  Definition binding' := binding var tyvar var tyvar.

  Definition free_vars_bindings (free_vars_binding : Recursivity -> binding' -> list var) :=
    fix free_vars_bindings rec (bs : list binding') : list var :=
    match rec with
      | Rec    =>
          delete_many var_eqb (bvbs bs) (concat (map (free_vars_binding Rec) bs))
      | NonRec =>
          match bs with
            | nil     => []
            | b :: bs => free_vars_binding NonRec b
                ++ delete_many var_eqb (bvb b) (free_vars_bindings NonRec bs)
          end
    end.


  Fixpoint free_vars (t : term var tyvar var tyvar) : list var :=
   match t with
     | Let rec bs t => free_vars_bindings free_vars_binding rec bs ++ delete_many var_eqb (bvbs bs) (free_vars t)
     | (LamAbs n ty t)   => delete var_eqb n (free_vars t)
     | (Var n)           => [n]
     | (TyAbs n k t)     => free_vars t
     | (Apply s t)       => free_vars s ++ free_vars t
     | (TyInst t ty)     => free_vars t
     | (IWrap ty1 ty2 t) => free_vars t
     | (Unwrap t)        => free_vars t
     | (Error ty)        => []
     | (Constant v)      => []
     | (Builtin f)       => []
     end

  with free_vars_binding rec (b : binding') : list var :=
    match b with
      | TermBind _ (VarDecl v _) t => match rec with
        | Rec    => delete var_eqb v (free_vars t)
        | NonRec => free_vars t
        end
      | _        => []
    end
    .

End FreeVars.

