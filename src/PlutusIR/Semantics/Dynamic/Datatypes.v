Require Import
  Strings.String
  Lists.List
.
From PlutusCert Require Import
  PlutusIR
  Util
.
Import PlutusNotations.
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
Definition mk_name : nat -> string :=
  string_of_nat
.


Section SOP_CONSTRUCTOR.

  (* Given a constructor with tag ix, SOP type τ_SOP, type parameters α_0 .. α_n and type
   *
   *    σ_0 -> ... -> σ_n -> τ
   *
   * builds a term of the form:
   *
   *    Λ α_0. ... Λ α_1. λ0. ... λ n. Constr τ_SOP ix [0, ... n]
  *)

  Context
    (ix : nat)     (* Index of the constructor *)
    (ty_sop : ty)  (* SOP representation of the ADT *)
  .

  (* Make SOP representation for monomorphic constructor *)
  Fixpoint mk_mono (ty_constr : ty) (n : nat) :=
    match ty_constr with
      | <{ σ  → τ }> => LamAbs (mk_name n) σ (mk_mono τ (1 + n))
      | _            => Constr ty_sop ix (map (Var ∘ mk_name) (seq 0 n))
    end
  .

  (* Make SOP representation for polymorphic constructor
   *)
  Fixpoint mk_poly (tyvars : list tvdecl) (ty_constr : ty) :=
    match tyvars with
      | []                      => mk_mono ty_constr 0
      | TyVarDecl α K :: tyvars => TyAbs α K (mk_poly tyvars ty_constr)
    end
  .

  Definition constr_to_subst (tyvars : list tvdecl) (c : vdecl)
    : string * term :=
    match c with
      VarDecl x τ => (x, mk_poly tyvars τ)
    end
  .

End SOP_CONSTRUCTOR.

Definition constrs_to_subst (ty_sop : ty) (tyvars : list tvdecl) (cs : list vdecl)
  : list (string * term) :=
  map (fun '(ix, c) => constr_to_subst ix ty_sop tyvars c) (zip_from 0 cs)
.

Definition compile_ty : recursivity -> dtdecl -> ty := fun _ _ => Ty_Var "<SOP>"%string.

(*
 * TODO compare with what the compiler does:
    see https://github.com/IntersectMBO/plutus/blob/16be7da33eacb1991ae0164b9fd65e12c7e4771e/plutus-core/plutus-ir/src/PlutusIR/Compiler/Datatype.hs#L414
 * https://github.com/IntersectMBO/plutus/blob/16be7da33eacb1991ae0164b9fd65e12c7e4771e/plutus-core/plutus-ir/src/PlutusIR/Compiler/Datatype.hs#L486
 *)
Axiom compile_match : dtdecl -> term.

Definition compile_constrs (compiled_ty : ty) (tyvars : list tvdecl) (cs : list vdecl)
  : list (string * term) :=
  map (fun '(ix, c) => constr_to_subst ix compiled_ty tyvars c) (zip_from 0 cs)
.

Definition compile_data (rec : recursivity) (dtd : dtdecl) :=
  match dtd with
  | Datatype (TyVarDecl X K) tvs m cs =>
      let ty_sop := compile_ty rec dtd in
      let t_match := compile_match dtd in
      let cs := compile_constrs ty_sop tvs cs in
      (ty_sop, t_match, cs)
  end
.




Section Test.
  Open Scope string.

  (* TODO: placeholder until Ty_SOP is part of type language *)
  Definition ty_fake := Ty_Builtin DefaultUniInteger.
  Compute (mk_poly 3 ty_fake [] (Ty_Fun (Ty_Var "a") (Ty_Fun (Ty_Var "b") (Ty_Var "c")))).
End Test.
