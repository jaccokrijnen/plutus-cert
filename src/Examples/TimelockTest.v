(* Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
*)

From PlutusCert Require Import 
  Examples.TimelockDumps
  Language.PlutusIR
  Language.PlutusIR.Transform.Inline
  Language.PlutusIR.Transform.Inline.DecOpt
  Language.PlutusIR.Transform.Inline.DecideBool.

From QuickChick Require Import QuickChick.

Import NamedTerm.


Definition pre : Term := (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("False") (Unique (3))))) (nil)) (Var (Name ("keep") (Unique (77))))).
Definition post : Term := (Let (NonRec) (cons (TermBind (NonStrict) (VarDecl (Name ("keep") (Unique (77))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("False") (Unique (3))))) (nil)) (Var (Name ("False") (Unique (3))))).

Compute (@decOpt (inline nil pir_3_1_inlined pir_3_1_inlined) _ 14).
Compute (@decOpt (inline nil pir_3_deadcode pir_3_1_inlined) _ 14).
