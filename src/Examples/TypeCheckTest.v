From PlutusCert Require Import
  PlutusIR
  Typechecker
.

Require Import Coq.Strings.String.
Open Scope string_scope.

Require Import Lists.List.
Import ListNotations.

Definition t := (LamAbs "x" (Ty_App (Ty_Lam "α" Kind_Base (Ty_Var "α")) (Ty_Builtin DefaultUniInteger)) (Var "x")).
Definition force_extract := t.

Definition t_type := type_check [] [] t.

From PlutusCert Require Import
  PlutusIR Parser
.
Import Parser.DumpNotations.
Open Scope pir_dump_scope.
From PlutusCert Require Import Typing.Typechecker.
 
Require Import ExtrHaskellZInteger.
(* For strings and chars *)
Require Import ExtrHaskellString.    (* string -> Haskell String, ascii -> Char *)

(* For lists and options *)
Require Import ExtrHaskellBasic.

Parameter show_Z : Z -> string.
Extract Constant show_Z => "show".

(* NOTE: Extraction may require some manual work. Such as adding Derive Show, etc.
   A working extraction (with minor manual work already performed) is found in TypeCheckTest.hs
*)
Extraction Language Haskell.

(* Uncomment this for extraction *)
(* Redirect "TypeCheckTest.hs" Recursive Extraction t_type. *)

