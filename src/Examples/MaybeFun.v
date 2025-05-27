From PlutusCert Require Import
  PlutusIR Parser
.
Import Parser.DumpNotations.
Open Scope pir_dump_scope.

(*
Last PIR term when compiling maybeFun in (Test.Optimization.Spec.hs)

maybeFun :: CompiledCode (Maybe Integer -> Maybe Integer -> Maybe Integer)
maybeFun = $$(compile
   [|| \(x :: Maybe Integer) (y :: Maybe Integer) ->
         case x of
            Just x' -> case y of
                 Just y' -> Just (x' `Builtins.addInteger` y')
                 Nothing -> Nothing
            Nothing -> Nothing
   ||])

*)

Definition maybeFun_compiled :=

  Let () NonRec (DatatypeBind () (Datatype () (TyVarDecl () (TyName (Name
  [x4d,x61,x79,x62,x65] (Unique 1619))) (KindArrow () (Type ()) (Type ())))
  [TyVarDecl () (TyName (Name [x61] (Unique 1623))) (Type ())] (Name
  [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 1622)) [VarDecl () (Name
  [x4a,x75,x73,x74] (Unique 1620)) (TyFun () (TyVar () (TyName (Name [x61]
  (Unique 1623)))) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65]
  (Unique 1619)))) (TyVar () (TyName (Name [x61] (Unique 1623)))))),VarDecl ()
  (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 1621)) (TyApp () (TyVar () (TyName
  (Name [x4d,x61,x79,x62,x65] (Unique 1619)))) (TyVar () (TyName (Name [x61]
  (Unique 1623)))))]) :| []) (LamAbs () (Name [x64,x73] (Unique 1624)) (TyApp ()
  (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1619)))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (LamAbs () (Name [x64,x73] (Unique 1625))
  (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1619))))
  (TyBuiltin () (SomeTypeIn DefaultUniInteger))) (TyInst () (Apply () (Apply ()
  (TyInst () (Apply () (TyInst () (Var () (Name
  [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 1622))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 1624))))
  (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 1626))) (Type ()) (TyApp
  () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1619)))) (TyBuiltin
  () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x78,x27] (Unique
  1627)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 1628))) (Type ()) (TyInst () (Apply () (Apply ()
  (TyInst () (Apply () (TyInst () (Var () (Name
  [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 1622))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 1625))))
  (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 1629))) (Type ()) (TyApp
  () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 1619)))) (TyBuiltin
  () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x79,x27] (Unique
  1630)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 1631))) (Type ()) (Apply () (TyInst () (Var () (Name
  [x4a,x75,x73,x74] (Unique 1620))) (TyBuiltin () (SomeTypeIn
  DefaultUniInteger))) (Apply () (Apply () (Builtin () AddInteger) (Var () (Name
  [x78,x27] (Unique 1627)))) (Var () (Name [x79,x27] (Unique 1630)))))))) (TyAbs
  () (TyName (Name [x64,x65,x61,x64] (Unique 1632))) (Type ()) (TyInst () (Var
  () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 1621))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))))) (TyForall () (TyName (Name
  [x64,x65,x61,x64] (Unique 1633))) (Type ()) (TyVar () (TyName (Name
  [x64,x65,x61,x64] (Unique 1633))))))))) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 1634))) (Type ()) (TyInst () (Var () (Name
  [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 1621))) (TyBuiltin () (SomeTypeIn
  DefaultUniInteger))))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique
  1635))) (Type ()) (TyVar () (TyName (Name [x64,x65,x61,x64] (Unique
  1635))))))))

.

