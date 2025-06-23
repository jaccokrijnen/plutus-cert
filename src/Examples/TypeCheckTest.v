From PlutusCert Require Import
  PlutusIR
  Typechecker
.

Require Import Coq.Strings.String.
Open Scope string_scope.

Require Import Lists.List.
Import ListNotations.

Definition t := (LamAbs "x" (Ty_Lam "α" Kind_Base (Ty_Var "α")) (Var "x")).

Definition t_type := type_check [] [] t.


