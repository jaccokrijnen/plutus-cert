From Coq Require Import
  Strings.String
  Lists.List
  ZArith.BinInt.

From PlutusCert Require Import
  Language.PlutusIR
  FreeVars
  BoundVars
  Equality
  Examples.Game.Trace
  Util
  Static
  Static.Implementations.Named
  .

(* Import UniqueTerm.*)
Import NamedTerm.
Import ListNotations.

Local Open Scope Z_scope.

Definition pass :=
  Let (NonRec) (
    cons (TermBind (Strict) (VarDecl (Name ("fixBy") (Unique (181)))
      (Ty_Forall (TyName (Name ("F") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (2)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (2)))))) (Ty_Var (TyName (Name ("Q") (Unique (2))))))) (Ty_Forall (TyName (Name ("Q") (Unique (3)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (4)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (4)))))))) (Ty_Forall (TyName (Name ("Q") (Unique (5)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (5)))))) (Ty_Var (TyName (Name ("Q") (Unique (5)))))))))))
      (TyAbs (TyName (Name ("F") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (LamAbs (Name ("by") (Unique (1))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (2)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (2)))))) (Ty_Var (TyName (Name ("Q") (Unique (2))))))) (Ty_Forall (TyName (Name ("Q") (Unique (3)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))))) (Apply (TyInst (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (TyAbs (TyName (Name ("b") (Unique (1)))) (Kind_Base) (LamAbs (Name ("f") (Unique (2))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (Apply (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("s") (Unique (1))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))) (Apply (Unwrap (Var (Name ("s") (Unique (1))))) (Var (Name ("s") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (IWrap (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (LamAbs (Name ("s") (Unique (3))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (LamAbs (Name ("x") (Unique (4))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Apply (Apply (Var (Name ("f") (Unique (2)))) (Apply (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("s") (Unique (1))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))) (Apply (Unwrap (Var (Name ("s") (Unique (1))))) (Var (Name ("s") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (Var (Name ("s") (Unique (3)))))) (Var (Name ("x") (Unique (4)))))))))))) (Ty_Forall (TyName (Name ("Q") (Unique (6)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (6)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (6))))))))) (Ty_Forall (TyName (Name ("Q") (Unique (7)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (7)))))) (Ty_Var (TyName (Name ("Q") (Unique (7)))))))) (LamAbs (Name ("rec") (Unique (8))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (9)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (9)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (9)))))))) (Ty_Forall (TyName (Name ("Q") (Unique (10)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (10)))))) (Ty_Var (TyName (Name ("Q") (Unique (10)))))))) (LamAbs (Name ("h") (Unique (11))) (Ty_Forall (TyName (Name ("Q") (Unique (12)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (12)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (12)))))))) (TyAbs (TyName (Name ("R") (Unique (13)))) (Kind_Base) (LamAbs (Name ("fr") (Unique (14))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("R") (Unique (13)))))) (Apply (TyInst (Apply (Var (Name ("by") (Unique (1)))) (TyAbs (TyName (Name ("Q") (Unique (15)))) (Kind_Base) (LamAbs (Name ("fq") (Unique (16))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Apply (TyInst (Apply (Var (Name ("rec") (Unique (8)))) (Var (Name ("h") (Unique (11))))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Apply (TyInst (Var (Name ("h") (Unique (11)))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Var (Name ("fq") (Unique (16))))))))) (Ty_Var (TyName (Name ("R") (Unique (13)))))) (Var (Name ("fr") (Unique (14)))))))))))))
    (nil))
  (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("fix2") (Unique (182))) (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Forall (TyName (Name ("b") (Unique (1)))) (Kind_Base) (Ty_Forall (TyName (Name ("a") (Unique (2)))) (Kind_Base) (Ty_Forall (TyName (Name ("b") (Unique (3)))) (Kind_Base) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (4))))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (4))))))))) (Ty_Forall (TyName (Name ("R") (Unique (5)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("R") (Unique (5))))))) (Ty_Var (TyName (Name ("R") (Unique (5))))))))))))) (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (TyAbs (TyName (Name ("b") (Unique (1)))) (Kind_Base) (TyAbs (TyName (Name ("a") (Unique (2)))) (Kind_Base) (TyAbs (TyName (Name ("b") (Unique (3)))) (Kind_Base) (LamAbs (Name ("f") (Unique (7))) (Ty_Forall (TyName (Name ("Q") (Unique (8)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (8))))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (8))))))))) (Apply (Apply (TyInst (Var (Name ("fixBy") (Unique (181)))) (Ty_Lam (TyName (Name ("X") (Unique (6)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("X") (Unique (6))))))))) (LamAbs (Name ("k") (Unique (9))) (Ty_Forall (TyName (Name ("Q") (Unique (10)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (10))))))) (Ty_Var (TyName (Name ("Q") (Unique (10))))))) (TyAbs (TyName (Name ("S") (Unique (11)))) (Kind_Base) (LamAbs (Name ("h") (Unique (12))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Ty_Var (TyName (Name ("S") (Unique (11))))))) (Apply (Apply (Var (Name ("h") (Unique (12)))) (LamAbs (Name ("x") (Unique (15))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Apply (TyInst (Var (Name ("k") (Unique (9)))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (LamAbs (Name ("f_0") (Unique (13))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (LamAbs (Name ("f_1") (Unique (14))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Apply (Var (Name ("f_0") (Unique (13)))) (Var (Name ("x") (Unique (15)))))))))) (LamAbs (Name ("x") (Unique (18))) (Ty_Var (TyName (Name ("a") (Unique (2))))) (Apply (TyInst (Var (Name ("k") (Unique (9)))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (LamAbs (Name ("f_0") (Unique (16))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (LamAbs (Name ("f_1") (Unique (17))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (2))))) (Ty_Var (TyName (Name ("b") (Unique (3)))))) (Apply (Var (Name ("f_1") (Unique (17)))) (Var (Name ("x") (Unique (18)))))))))))))) (Var (Name ("f") (Unique (7))))))))))) (nil)) (Apply (Apply (Apply (TyInst (TyAbs (TyName (Name ("Bool") (Unique (1)))) (Kind_Base) (LamAbs (Name ("True") (Unique (2))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("False") (Unique (3))) (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (LamAbs (Name ("Bool_match") (Unique (4))) (Ty_Fun (Ty_Var (TyName (Name ("Bool") (Unique (1))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (173)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("lessThanEqInteger") (Unique (30))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Fun (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))))) (LamAbs (Name ("arg") (Unique (31))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (LamAbs (Name ("arg") (Unique (32))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("b") (Unique (33))) (Ty_Builtin (Some (TypeIn (DefaultUniBool)))) (Apply (Apply (Apply (TyInst (Builtin (IfThenElse)) (Ty_Var (TyName (Name ("Bool") (Unique (1)))))) (Var (Name ("b") (Unique (33))))) (Var (Name ("True") (Unique (2))))) (Var (Name ("False") (Unique (3)))))) (Apply (Apply (Builtin (LessThanEqInteger)) (Var (Name ("arg") (Unique (31))))) (Var (Name ("arg") (Unique (32))))))))) (nil)) (LamAbs (Name ("ds") (Unique (71))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))) (Apply (LamAbs (Name ("tup") (Unique (185))) (Ty_Forall (TyName (Name ("r") (Unique (186)))) (Kind_Base) (Ty_Fun (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Ty_Var (TyName (Name ("r") (Unique (186))))))) (Ty_Var (TyName (Name ("r") (Unique (186))))))) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("w") (Unique (72))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))))) (Apply (TyInst (Var (Name ("tup") (Unique (185)))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))))) (LamAbs (Name ("arg_0") (Unique (187))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (LamAbs (Name ("arg_1") (Unique (188))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Var (Name ("arg_0") (Unique (187)))))))) (nil)) (Let (NonRec) (cons (TermBind (Strict) (VarDecl (Name ("z") (Unique (73))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))))) (Apply (TyInst (Var (Name ("tup") (Unique (185)))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger)))))) (LamAbs (Name ("arg_0") (Unique (189))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (LamAbs (Name ("arg_1") (Unique (190))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Var (Name ("arg_1") (Unique (190)))))))) (nil)) (Apply (Apply (Var (Name ("lessThanEqInteger") (Unique (30)))) (Apply (Var (Name ("z") (Unique (73)))) (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("x") (Unique (1))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Var (Name ("x") (Unique (1)))))))) (Apply (Var (Name ("w") (Unique (72)))) (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("x") (Unique (1))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Var (Name ("x") (Unique (1))))))))))) (Apply (TyInst (TyInst (TyInst (TyInst (Var (Name ("fix2") (Unique (182)))) (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (TyAbs (TyName (Name ("Q") (Unique (183)))) (Kind_Base) (LamAbs (Name ("choose") (Unique (184))) (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Ty_Var (TyName (Name ("Q") (Unique (183))))))) (LamAbs (Name ("w") (Unique (72))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (LamAbs (Name ("z") (Unique (73))) (Ty_Fun (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Ty_Builtin (Some (TypeIn (DefaultUniInteger))))) (Apply (Apply (Var (Name ("choose") (Unique (184)))) (LamAbs (Name ("arg") (Unique (171))) (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Apply (Apply (Builtin (AddInteger)) (Var (Name ("ds") (Unique (71))))) (Apply (Var (Name ("z") (Unique (73)))) (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("x") (Unique (1))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Var (Name ("x") (Unique (1)))))))))) (LamAbs (Name ("arg") (Unique (172))) (Ty_Forall (TyName (Name ("a") (Unique (0)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (0))))))) (Apply (Apply (Builtin (AddInteger)) (Var (Name ("ds") (Unique (71))))) (Apply (Var (Name ("w") (Unique (72)))) (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("x") (Unique (1))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Var (Name ("x") (Unique (1)))))))))))))))))))))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (173)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (174)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (175))) (Ty_Var (TyName (Name ("out_Bool") (Unique (174))))) (LamAbs (Name ("case_False") (Unique (176))) (Ty_Var (TyName (Name ("out_Bool") (Unique (174))))) (Var (Name ("case_True") (Unique (175)))))))) (TyAbs (TyName (Name ("out_Bool") (Unique (177)))) (Kind_Base) (LamAbs (Name ("case_True") (Unique (178))) (Ty_Var (TyName (Name ("out_Bool") (Unique (177))))) (LamAbs (Name ("case_False") (Unique (179))) (Ty_Var (TyName (Name ("out_Bool") (Unique (177))))) (Var (Name ("case_False") (Unique (179)))))))) (LamAbs (Name ("x") (Unique (180))) (Ty_Forall (TyName (Name ("out_Bool") (Unique (173)))) (Kind_Base) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Fun (Ty_Var (TyName (Name ("out_Bool") (Unique (173))))) (Ty_Var (TyName (Name ("out_Bool") (Unique (173)))))))) (Var (Name ("x") (Unique (180)))))))
.

Definition fixBy_type :=
  (Ty_Forall (TyName (Name ("F") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Fun (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (2)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (2)))))) (Ty_Var (TyName (Name ("Q") (Unique (2))))))) (Ty_Forall (TyName (Name ("Q") (Unique (3)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (4)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (4)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (4)))))))) (Ty_Forall (TyName (Name ("Q") (Unique (5)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (5)))))) (Ty_Var (TyName (Name ("Q") (Unique (5))))))))))
.

Definition fixBy :=
 TyAbs (TyName (Name ("F") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (LamAbs (Name ("by") (Unique (1))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (2)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (2)))))) (Ty_Var (TyName (Name ("Q") (Unique (2))))))) (Ty_Forall (TyName (Name ("Q") (Unique (3)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))) (Ty_Var (TyName (Name ("Q") (Unique (3)))))))) (Apply (TyInst (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (TyAbs (TyName (Name ("b") (Unique (1)))) (Kind_Base) (LamAbs (Name ("f") (Unique (2))) (Ty_Fun (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (Apply (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("s") (Unique (1))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))) (Apply (Unwrap (Var (Name ("s") (Unique (1))))) (Var (Name ("s") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (IWrap (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1)))))) (LamAbs (Name ("s") (Unique (3))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (LamAbs (Name ("x") (Unique (4))) (Ty_Var (TyName (Name ("a") (Unique (0))))) (Apply (Apply (Var (Name ("f") (Unique (2)))) (Apply (TyInst (TyAbs (TyName (Name ("a") (Unique (0)))) (Kind_Base) (LamAbs (Name ("s") (Unique (1))) (Ty_App (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_IFix (Ty_Lam (TyName (Name ("self") (Unique (0)))) (Kind_Arrow (Kind_Base) (Kind_Base)) (Ty_Lam (TyName (Name ("a") (Unique (1)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("self") (Unique (0))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))) (Ty_Var (TyName (Name ("a") (Unique (1)))))))) (Ty_Var (TyName (Name ("a") (Unique (1))))))) (Ty_Var (TyName (Name ("a") (Unique (0)))))) (Apply (Unwrap (Var (Name ("s") (Unique (1))))) (Var (Name ("s") (Unique (1))))))) (Ty_Fun (Ty_Var (TyName (Name ("a") (Unique (0))))) (Ty_Var (TyName (Name ("b") (Unique (1))))))) (Var (Name ("s") (Unique (3)))))) (Var (Name ("x") (Unique (4)))))))))))) (Ty_Forall (TyName (Name ("Q") (Unique (6)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (6)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (6))))))))) (Ty_Forall (TyName (Name ("Q") (Unique (7)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (7)))))) (Ty_Var (TyName (Name ("Q") (Unique (7)))))))) (LamAbs (Name ("rec") (Unique (8))) (Ty_Fun (Ty_Forall (TyName (Name ("Q") (Unique (9)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (9)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (9)))))))) (Ty_Forall (TyName (Name ("Q") (Unique (10)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (10)))))) (Ty_Var (TyName (Name ("Q") (Unique (10)))))))) (LamAbs (Name ("h") (Unique (11))) (Ty_Forall (TyName (Name ("Q") (Unique (12)))) (Kind_Base) (Ty_Fun (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (12)))))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (12)))))))) (TyAbs (TyName (Name ("R") (Unique (13)))) (Kind_Base) (LamAbs (Name ("fr") (Unique (14))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("R") (Unique (13)))))) (Apply (TyInst (Apply (Var (Name ("by") (Unique (1)))) (TyAbs (TyName (Name ("Q") (Unique (15)))) (Kind_Base) (LamAbs (Name ("fq") (Unique (16))) (Ty_App (Ty_Var (TyName (Name ("F") (Unique (0))))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Apply (TyInst (Apply (Var (Name ("rec") (Unique (8)))) (Var (Name ("h") (Unique (11))))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Apply (TyInst (Var (Name ("h") (Unique (11)))) (Ty_Var (TyName (Name ("Q") (Unique (15)))))) (Var (Name ("fq") (Unique (16))))))))) (Ty_Var (TyName (Name ("R") (Unique (13)))))) (Var (Name ("fr") (Unique (14)))))))))))
.


(* This could perhaps be an additional rule (to much work now to add it,
change all existing proofs) *)
Axiom T_Normalize : forall ctx t S T,
  S =b T ->
  (ctx |-+ t : S) ->
  (ctx |-+ t : T).

Lemma fixBy_tc :
  emptyContext |-+ fixBy : fixBy_type.
Proof.
  unfold fixBy, fixBy_type.
  apply T_TyAbs.
  apply T_LamAbs.
  eapply T_Apply.
  { eapply T_TyInst.
    { eapply T_TyInst.
      { apply T_TyAbs.
        apply T_TyAbs.
        apply T_LamAbs.
        eapply T_Apply.
        { eapply T_TyInst.
          { apply T_TyAbs.
            apply T_LamAbs.
            eapply T_Apply.
              { eapply T_Unwrap.
                { eapply T_Normalize.
                  2: {apply T_Var. reflexivity. }
                  { apply beta_reduce_EqT. reflexivity. }
                }
                { simpl. eapply K_Var. reflexivity. }
                { simpl.
                  unfold unwrapIFix, TyName, Name.
                  apply beta_reduce_EqT.
                  simpl.
                  reflexivity.
                }
              }

Abort. (* WIP *)

            (* reflexivity.*)
            (* cbv.*)
            (* Stuck since we need to normalize the type in the environment *)




(*

(termbind
    (strict)
    (vardecl
      fixBy
      (all F (fun (type) (type))
        (fun
          (fun (all Q (type) (fun [F Q] Q)) (all Q (type) (fun [F Q] Q)))
          (fun (all Q (type) (fun [F Q] [F Q])) (all Q (type) (fun [F Q] Q)))))
    )
    (abs
      F
      (fun (type) (type))
      (lam
        by
        (fun (all Q (type) (fun [F Q] Q)) (all Q (type) (fun [F Q] Q)))
        [
          {
            {
              (abs
                a
                (type)
                (abs
                  b
                  (type)
                  (lam
                    f
                    (fun (fun a b) (fun a b))
                    [
                      {
                        (abs
                          a
                          (type)
                          (lam
                            s
                            [(lam a (type) (ifix (lam self (fun (type) (type)) (lam a (type) (fun [self a] a))) a)) a]
                            [ (unwrap s) s ]
                          )
                        )
                        (fun a b)
                      }
                      (iwrap
                        (lam self (fun (type) (type)) (lam a (type) (fun [self a] a)))
                        (fun a b)
                        (lam
                          s
                          [(lam a (type) (ifix (lam self (fun (type) (type)) (lam a (type) (fun [self a] a))) a)) (fun a b)]
                          (lam
                            x
                            a
                            [
                              [
                                f
                                [
                                  {
                                    (abs
                                      a
                                      (type)
                                      (lam
                                        s
                                        [(lam a (type) (ifix (lam self (fun (type) (type)) (lam a (type) (fun [self a] a))) a)) a]
                                        [ (unwrap s) s ]
                                      )
                                    )
                                    (fun a b)
                                  }
                                  s
                                ]
                              ]
                              x
                            ]
                          )
                        )
                      )
                    ]
                  )
                )
              )
              (all Q (type) (fun [F Q] [F Q]))
            }
            (all Q (type) (fun [F Q] Q))
          }
          (lam
            rec
            (fun (all Q (type) (fun [F Q] [F Q])) (all Q (type) (fun [F Q] Q)))
            (lam
              h
              (all Q (type) (fun [F Q] [F Q]))
              (abs
                R
                (type)
                (lam
                  fr
                  [F R]
                  [
                    {
                      [
                        by
                        (abs
                          Q
                          (type)
                          (lam fq [F Q] [ { [ rec h ] Q } [ { h Q } fq ] ])
                        )
                      ]
                      R
                    }
                    fr
                  ]
                )
              )
            )
          )
        ]
      )
    )
  )

*)
