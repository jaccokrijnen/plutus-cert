Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  PlutusIR
  Util
.

Import ListNotations.

(* Constructing constructor functions from their type signature *)

(* Note [ Generating names ]

  Since on the term-level, the operational semantics never substitutes open
  terms, variable capture cannot happen.
*)


(* TODO compute SOP type from datatype declaration, when Ty_SOP is part of type
 * language.
 *)
Axiom mk_SOP_ty : dtdecl -> ty.

(* See note [Generating names] *)
Definition mkName : nat -> string :=
  string_of_nat
.

(* See constr_to_term *)
Fixpoint constr_to_term_mono (ix : nat) (ty_sop : ty) (ty_constr : ty) (n : nat) :=
  match ty_constr with
    | Ty_Fun σ τ => LamAbs (mkName n) σ (constr_to_term_mono ix ty_sop τ (S n))
    | _          => Constr ix ty_sop (map (Var ∘ mkName) (seq 0 n))
  end
.



(* Given a constructor with tag ix, SOP type τ_SOP, type parameters α_0 .. α_n and type
 *
 *    σ_0 -> ... -> σ_n -> τ
 *
 * builds a term of the form:
 *
 *    Λ α_0. ... Λ α_1. λ0. ... λ n. Constr ix τ_SOP [0, ... n]
 *)
Fixpoint constr_to_term (ix : nat) (ty_sop : ty) (tyvars : list tvdecl) (ty_constr : ty) :=
  match tyvars with
    | []                      => constr_to_term_mono ix ty_sop ty_constr 0
    | TyVarDecl α K :: tyvars => TyAbs α K (constr_to_term ix ty_sop tyvars ty_constr)
  end
.


(*
 * TODO compare with what the compiler does: 
    see https://github.com/IntersectMBO/plutus/blob/16be7da33eacb1991ae0164b9fd65e12c7e4771e/plutus-core/plutus-ir/src/PlutusIR/Compiler/Datatype.hs#L414
*)

Axiom constr_to_subst : list tvdecl -> nat -> vdecl -> string * term.
(*
Definition constr_to_subst (tyvars : list TVDecl) (ix : nat) (c : constructor)
  : string * Term :=
  match c with
    Constructor (VarDecl x τ) _arity => (x, constr_to_term ix tyvars τ)
  end
.
  *)

Definition constrs_to_subst (tyvars : list tvdecl) (cs : list vdecl)
  : list (string * term) :=
  map (uncurry (constr_to_subst tyvars)) (zip_from 0 cs)
.

Axiom dt_to_ty : dtdecl -> ty.

(* TODO compare with compiler implementation:
 * https://github.com/IntersectMBO/plutus/blob/16be7da33eacb1991ae0164b9fd65e12c7e4771e/plutus-core/plutus-ir/src/PlutusIR/Compiler/Datatype.hs#L486
 *)
Axiom match_to_term : dtdecl -> term.

Definition dt_subst (dtd : dtdecl) : ty * term * list (string * term) :=
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

  (* TODO: placeholder until Ty_SOP is part of type language *)
  Definition ty_fake := Ty_Builtin DefaultUniInteger.
  Compute (constr_to_term 3 ty_fake [] (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "b") (Ty_Var "c")))).
End Test.
