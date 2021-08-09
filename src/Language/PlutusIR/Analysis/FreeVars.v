Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Ascii.
Require Import Omega.
From Equations Require Import Equations.

Set Implicit Arguments.

From PlutusCert Require Import Language.PlutusIR.
From PlutusCert Require Import Language.PlutusIR.Folds.

Local Open Scope string_scope.

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

Definition remove_list {A} (dec : forall x y, {x = y} + {x <> y}) : list A -> list A -> list A :=
  fun rs xs => fold_right (remove dec) xs rs.

Fixpoint remove_eqb {a} a_eqb xs : list a :=
  match xs with
    | nil => nil
    | x :: xs => if a_eqb x : bool then remove_eqb a_eqb xs else x :: remove_eqb a_eqb xs
  end
  .

Section FreeVars.
  Context
    {var : Set}
    (var_eqb : var -> var -> bool)
    .

Fixpoint boundVars (bs : list (binding var)) : list var := match bs with
    | ((TermBind _ (VarDecl v _) t) :: bs) => v :: boundVars bs
    | (b                :: bs) =>      boundVars bs
    | nil               => nil
    end.

Fixpoint boundTerms (bs : list (binding var)) : list (var * term var) := match bs with
    | ((TermBind _ (VarDecl v _) t) :: bs) => (v, t) :: boundTerms bs
    | (b                :: bs) =>           boundTerms bs
    | nil               => nil
    end.

Definition delete : var -> list var -> list var :=
  fun x xs => filter (fun y => negb (var_eqb x y)) xs.

Definition elem x xs := existsb (var_eqb x) xs.

Definition deleteMany : list var -> list var -> list var :=
  fun ds xs => filter (fun x => negb (elem x ds)) xs.

Fixpoint freeVars (t : term var) : list var :=
 match t with
   | (Let Rec bs t)    => deleteMany (boundVars bs) (freeVars t ++ concat (map freeVarsBinding bs))
   | (Let NonRec bs t) => fold_right
                            (fun b fv_bs bound => match b with
                               | TermBind s (VarDecl v _) t => app (deleteMany bound (freeVarsBinding b)) (fv_bs (v :: bound))
                               | _              => fv_bs bound
                               end
                            )
                            (fun _ => nil)
                            bs
                            []
   | (LamAbs n ty t)   => delete n (freeVars t)
   | (Var n)           => [n]
   | (TyAbs n k t)     => freeVars t
   | (Apply s t)       => freeVars s ++ freeVars t
   | (TyInst t ty)     => freeVars t
   | (IWrap ty1 ty2 t) => freeVars t
   | (Unwrap t)        => freeVars t
   | (Error ty)        => []
   | (Constant v)      => []
   | (Builtin f)       => []
   end

with freeVarsBinding (b : binding var) :=
  match b with
    | TermBind _ v t => freeVars t
    | _              => []
  end
  .

End FreeVars.


Equations fv' : Term -> list string := {
  fv' (Let rec bs t)    := let fvs := app (fv_bindings bs) (fv' t)
                           in  remove_list string_dec (boundVars bs) fvs;
  fv' (LamAbs n ty t)   := remove string_dec n (fv' t);
  fv' (Var n)           := n :: nil;
  fv' (TyAbs n k t)     := fv' t;
  fv' (Apply s t)       := fv' s ++ fv' t;
  fv' (TyInst t ty)     := fv' t;
  fv' (IWrap ty1 ty2 t) := fv' t;
  fv' (Unwrap t)        := fv' t;
  fv' (Error ty)        := nil;
  fv' (Constant v)      := nil;
  fv' (Builtin f)       := nil
  }
  where fv_bindings : list Binding -> list string := {
    fv_bindings ((TermBind _ (VarDecl n _) t) :: bs) := cons n (fv_bindings bs) ++ fv' t;
    fv_bindings (_                :: bs) := fv_bindings bs;
    fv_bindings nil                      := nil
  }
  .

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
(*
(* TODO: use well-founded recursion to include the subterms of
let-bindings *)
Fixpoint freeVars (t : Term) : list name := match t with
    | Let _ bs t   =>
        let ts_let    := map (fun x => match x with
          | TermBind _ _ t => Datatypes.Some t
          | _              => None end) bs in
        let fvs_let   := nil in (* freeVars_binders bs in *) (* TODO *)
        let fvs_t     := freeVars t in
        let names_let := catMaybes (map boundName bs) in
          fold_right (remove name_dec) (app fvs_let fvs_t) names_let

    | LamAbs n _ t => remove name_dec n (freeVars t)

    | Var n        => n :: nil
    | TyAbs _ _ t  => freeVars t
    | Apply t1 t2  => freeVars t1 ++ freeVars t2
    | TyInst t _   => freeVars t
    | Unwrap t     => freeVars t
    | IWrap _ _ t  => freeVars t
    | Constant _   => nil
    | Builtin _    => nil
    | Error _      => nil
    end
.

Fixpoint freeVars_binders (b : list Binding) : list name := match b with
  | cons (TermBind _ _ t) xs => freeVars t ++ freeVars_binders xs
  | cons _ xs => freeVars_binders xs
  | nil => nil
end
.
*)
