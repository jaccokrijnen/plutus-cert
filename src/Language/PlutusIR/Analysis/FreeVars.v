Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import
  Language.PlutusIR
  Language.PlutusIR.Folds
  Util.


(* Parametrized for _named_ binders (not de Bruijn) *)
Section FreeVars.
  Context
    {var tyvar : Set}
    (var_eqb : var -> var -> bool)
    .

Notation term'    := (term var tyvar var tyvar).
Notation binding' := (binding var tyvar var tyvar).

Fixpoint bound_vars_binding (b : binding') : list var := match b with
  | TermBind _ (VarDecl v _) _ => [v]
  | DatatypeBind (Datatype _ _ matchf constructors ) => [matchf] ++ map constructorName constructors
  | _                          => []
  end.

Fixpoint bound_vars_bindings (bs : list binding') : list var := match bs with
    | (b :: bs)
        => bound_vars_binding b ++ bound_vars_bindings bs
    | nil       => nil
    end.

Fixpoint boundTerms_bindings (bs : list binding') : list (var * term var tyvar var tyvar) := match bs with
    | ((TermBind _ (VarDecl v _) t) :: bs) => (v, t) :: boundTerms_bindings bs
    | (b                :: bs) =>           boundTerms_bindings bs
    | nil               => nil
    end.

Definition delete_all : var -> list var -> list var :=
  fun x xs => filter (fun y => negb (var_eqb x y)) xs.

Fixpoint delete (x : var) (xs : list var) : list var :=
  match xs with
    | nil => nil
    | cons y ys => if var_eqb x y then ys else y :: delete x ys
  end.

Definition elem x xs := existsb (var_eqb x) xs.

Definition delete_all_many : list var -> list var -> list var :=
  fun ds xs => filter (fun x => negb (elem x ds)) xs.


Section fvbs.
(*
  Workaround for: Cannot guess decreasing argument of fix (in free_vars/free_vars_binding)
*)
Context (free_vars_binding : Recursivity -> binding' -> list var).

Fixpoint free_vars_bindings  rec (bs : list binding') : list var :=
  match rec with
    | Rec    =>
        delete_all_many (bound_vars_bindings bs) (concat (map (free_vars_binding Rec) bs))
    | NonRec =>
        match bs with
          | nil     => []
          | b :: bs => free_vars_binding NonRec b
                       ++ delete_all_many (bound_vars_binding b) (free_vars_bindings NonRec bs)
        end
  end.
End fvbs.


Fixpoint free_vars (t : term var tyvar var tyvar) : list var :=
 match t with
   | Let rec bs t => free_vars_bindings free_vars_binding rec bs ++ delete_all_many (bound_vars_bindings bs) (free_vars t)
   | (LamAbs n ty t)   => delete_all n (free_vars t)
   | (Var n)           => [n]
   | (TyAbs n k t)     => free_vars t
   | (Apply s t)       => free_vars s ++ free_vars t
   | (TyInst t ty)     => free_vars t
   | (IWrap ty1 ty2 t) => free_vars t
   | (Unwrap t)        => free_vars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   | (ExtBuiltin f args) => concat (map free_vars args)
   end

with free_vars_binding rec (b : binding') : list var :=
  match b with
    | TermBind _ (VarDecl v _) t => match rec with
      | Rec    => delete_all v (free_vars t)
      | NonRec => free_vars t
      end
    | _        => []
  end
  .

End FreeVars.


(*
Equations fv' : Term -> list string := {
  fv' (Let rec bs t)    := let fvs := app (fv_bindings bs) (fv' t)
                           in  remove_list string_dec (bound_vars_bindings bs) fvs;
  fv' (LamAbs n ty t)   := remove string_dec n (fv' t);
  fv' (Var n)           := n :: nil;
  fv' (TyAbs n k t)     := fv' t;
  fv' (Apply s t)       := fv' s ++ fv' t;
  fv' (TyInst t ty)     := fv' t;
  fv' (IWrap ty1 ty2 t) := fv' t;
  fv' (Unwrap t)        := fv' t;
  fv' (Error ty)        := nil;
  fv' (Constant v)      := nil;
  fv' (Builtin f)       := nil;
  fv' (ExtBuiltin f args) := concat (map fv' args)
  }
  where fv_bindings : list Binding -> list string := {
    fv_bindings ((TermBind _ (VarDecl n _) t) :: bs) := cons n (fv_bindings bs) ++ fv' t;
    fv_bindings (_                :: bs) := fv_bindings bs;
    fv_bindings nil                      := nil
  }
  .
*)

(* Apparently, Equations did something special, since the similar definition below
  is not allowed in plain gallina.

  Recursive definition of fvs_bindings is ill-formed.
  ...
  Recursive call [in fvs_bindings] to fvs has principal argument equal to t *)
(*
Fixpoint fvs (t : Term) : list string := match t with
  | (Let rec bs t)    => let vars := app (fvs_bindings bs) (fvs t)
                         in  fold_right (remove string_dec) vars (binders bs)
  | (Var n)           => n :: nil
  | (TyAbs n k t)     => fvs t
  | (LamAbs n ty t)   => remove string_dec n (fvs t)
  | (Apply s t)       => app (fvs s) (fvs t)
  | (TyInst t ty)     => fvs t
  | (IWrap ty1 ty2 t) => fvs t
  | (Unwrap t)        => fvs t
  | (Error ty)        => nil
  | (Constant v)      => nil
  | (Builtin f)       => nil
  end
  with fvs_bindings (bs : list Binding) : list string := match bs with
    | ((TermBind _ (VarDecl n _ ) t) :: bs) => cons n (fvs_bindings bs) ++ fvs t
    | (b :: bs)                             => fvs_bindings bs
    | nil                                   => nil
    end
.
*)

(*
Fixpoint catMaybes {a : Type} (xs : list (option a)) : list a := match xs with
  | nil => nil
  | cons (Datatypes.Some x) xs => cons x (catMaybes xs)
  | cons _ xs => catMaybes xs
  end.

Definition boundName : Binding -> option name := fun b =>
  match b with
    | TermBind _ (VarDecl v _) _ => Datatypes.Some v
    | _ => None
    end.

*)
(*
(* TODO: use well-founded recursion to include the subterms of
let-bindings *)
Fixpoint free_vars (t : Term) : list name := match t with
    | Let _ bs t   =>
        let ts_let    := map (fun x => match x with
          | TermBind _ _ t => Datatypes.Some t
          | _              => None end) bs in
        let fvs_let   := nil in (* free_vars_binders bs in *) (* TODO *)
        let fvs_t     := free_vars t in
        let names_let := catMaybes (map boundName bs) in
          fold_right (remove name_dec) (app fvs_let fvs_t) names_let

    | LamAbs n _ t => remove name_dec n (free_vars t)

    | Var n        => n :: nil
    | TyAbs _ _ t  => free_vars t
    | Apply t1 t2  => free_vars t1 ++ free_vars t2
    | TyInst t _   => free_vars t
    | Unwrap t     => free_vars t
    | IWrap _ _ t  => free_vars t
    | Constant _   => nil
    | Builtin _    => nil
    | Error _      => nil
    end
.

Fixpoint free_vars_binders (b : list Binding) : list name := match b with
  | cons (TermBind _ _ t) xs => free_vars t ++ free_vars_binders xs
  | cons _ xs => free_vars_binders xs
  | nil => nil
end
.
*)

(*
Definition fv_alg :=
  {| A_Var      := fun n        => cons n nil
  ;  A_LamAbs   := fun n _ fvs  => remove string_dec n fvs

  ;  A_Let      := fun _ bs fvs => fvs (*TODO let bindings*)

  ;  A_Apply    := fun fvs fvs' => app fvs fvs'
  ;  A_TyAbs    := fun _ _ fvs  => fvs
  ;  A_TyInst   := fun fvs _    => fvs
  ;  A_IWrap    := fun _ _ fvs  => fvs
  ;  A_Unwrap   := fun fvs      => fvs
  ;  A_Constant := fun _        => nil
  ;  A_Builtin  := fun _        => nil
  ;  A_Error    := fun _        => nil
  |}.

Definition FV : Term -> list string -> Type := Fold (fv_alg).

Example FV_test : FV (Var "test") (cons "test" nil).
Proof.
  constructor.
Qed.

Definition fv := fold (fv_alg).
Example fv_test : fv (Var "test") = (cons "test" nil).
Proof.
  constructor.
Qed.

*)

