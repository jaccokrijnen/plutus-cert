Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  PlutusIR
  Util
.

Import NamedTerm.
Import ListNotations.



(* Note [ Generating names ]

  Since on the term-level, the operational semantics never substitutes open
  terms, variable capture cannot happen.

*)

(* See note [Generating names] *)
Definition mkName : nat -> string :=
  fun n => (Name "" n)
.

(* See constr_to_term *)
Fixpoint constr_to_term_mono (ix : nat) (τ : Ty) (n : nat) :=
  match τ with
    | Ty_Fun σ τ => LamAbs (mkName n) σ (constr_to_term_mono ix τ (S n))
    | _          => Constr ix (map (Var ∘ mkName) (seq 0 n))
  end
.

(* Given a constructor with tag ix, type parameters α_0 .. α_n and type
 *
 *    σ_0 -> ... -> σ_n -> τ
 *
 * builds a term of the form:
 *
 *    Λ α_0. ... Λ α_1. λ0. ... λ n. Constr ix [0, ... n]
 *)
Fixpoint constr_to_term (ix : nat) (tyvars : list TVDecl) (τ : Ty) :=
  match tyvars with
    | []                      => constr_to_term_mono ix τ 0
    | TyVarDecl α K :: tyvars => TyAbs α K (constr_to_term ix tyvars τ)
  end
.

Definition constr_to_subst (tyvars : list TVDecl) (ix : nat) (c : constructor)
  : string * Term :=
  match c with
    Constructor (VarDecl x τ) _arity => (x, constr_to_term ix tyvars τ)
  end
.

Definition constrs_to_subst (tyvars : list TVDecl) (cs : list constructor)
  : list (string * Term) :=
  map (uncurry (constr_to_subst tyvars)) (zip_from 0 cs)
.

Axiom dt_to_ty : DTDecl -> Ty.
Axiom match_to_term : DTDecl -> Term.

Definition dt_subst (dtd : DTDecl) : Ty * Term * list (string * Term) :=
  match dtd with
    | Datatype tvd tyvars matchf cs =>
       ( dt_to_ty dtd
       , match_to_term dtd
       , constrs_to_subst tyvars cs
       )
  end
.




Section Test.
  Open Scope string.
  Compute (constr_to_term 3 [] (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "b") (Ty_Var "c")))).
End Test.
