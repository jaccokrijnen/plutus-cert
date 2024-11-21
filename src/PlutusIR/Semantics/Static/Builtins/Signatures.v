From Coq Require Import
  Strings.String
.
From PlutusCert Require Import
  PlutusIR
  Values
.
Import PlutusNotations.

(*
This is based on the Plutus Core spec, which has the same built-ins and
defines their types and semantics (See Plutus Core Specification at
https://github.com/IntersectMBO/plutus#specifications-and-design

We don't model semantic variants of the ledger language yet. Builtins like
cons_bytestring have different meaning depending on the ledger language.
*)

(*
Signatures of built-in functions: allows to determine the arity and their
type.
*)
Inductive builtin_sig :=
  | BS_Forall : string -> kind -> builtin_sig -> builtin_sig
  | BS_Fun : ty -> builtin_sig -> builtin_sig
  | BS_Result : ty -> builtin_sig
.

Scheme Equality for builtin_sig.

#[local]
Notation "A '→' B" := (BS_Fun A B) (at level 49, right associativity).

Fixpoint to_ty (s : builtin_sig) : ty :=
  match s with
  | T → s => <{ T → {to_ty s} }>
  | BS_Forall X K s => Ty_Forall X K (to_ty s)
  | BS_Result T => T
  end
.

Fixpoint sig_arity (s : builtin_sig) : nat :=
  match s with
  | T → s => 1 + sig_arity s
  | BS_Forall _ _ s => 1 + sig_arity s
  | BS_Result _ => 0
  end
.


Local Open Scope string_scope.
(* Signatures of built-in functions *)
Definition to_sig (f : DefaultFun) : builtin_sig :=
  match f with
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger => <{ℤ}> → <{ℤ}> → BS_Result <{ℤ}>

  | EqualsInteger => <{ℤ}> → <{ℤ}> → BS_Result <{bool}>

  | IfThenElse => BS_Forall "A" Kind_Base (<{bool}> → Ty_Var "A" → Ty_Var "A" → BS_Result (Ty_Var "A"))

  | AppendByteString => <{ bytestring }> → <{ bytestring }> → BS_Result <{ bytestring }>

  (* TODO: see Plutus Core Spec *)
  | _ => <{ℤ}> → BS_Result <{ℤ}>
  end
.

(* Arity of built-in functions *)
(* TODO: For some reason, this doesn't evaluate fully under simpl *)
Definition arity (f : DefaultFun) : nat :=
  sig_arity (to_sig f)
.
