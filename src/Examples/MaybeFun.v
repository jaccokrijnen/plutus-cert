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

  Apply () (Apply () (Apply () (TyInst () (TyAbs () (TyName (Name
  [x4d,x61,x79,x62,x65] (Unique 3172))) (KindArrow () (Type ()) (Type ()))
  (LamAbs () (Name [x4a,x75,x73,x74] (Unique 3173)) (TyForall () (TyName (Name
  [x61] (Unique 3174))) (Type ()) (TyFun () (TyVar () (TyName (Name [x61]
  (Unique 3174)))) (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65]
  (Unique 3172)))) (TyVar () (TyName (Name [x61] (Unique 3174))))))) (LamAbs ()
  (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 3175)) (TyForall () (TyName (Name
  [x61] (Unique 3176))) (Type ()) (TyApp () (TyVar () (TyName (Name
  [x4d,x61,x79,x62,x65] (Unique 3172)))) (TyVar () (TyName (Name [x61] (Unique
  3176)))))) (LamAbs () (Name [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68]
  (Unique 3177)) (TyForall () (TyName (Name [x61] (Unique 3178))) (Type ())
  (TyFun () (TyApp () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique
  3172)))) (TyVar () (TyName (Name [x61] (Unique 3178))))) (TyForall () (TyName
  (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3179))) (Type ()) (TyFun
  () (TyFun () (TyVar () (TyName (Name [x61] (Unique 3178)))) (TyVar () (TyName
  (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3179))))) (TyFun () (TyVar
  () (TyName (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3179)))) (TyVar
  () (TyName (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3179)))))))))
  (LamAbs () (Name [x64,x73] (Unique 3180)) (TyApp () (TyVar () (TyName (Name
  [x4d,x61,x79,x62,x65] (Unique 3172)))) (TyBuiltin () (SomeTypeIn
  DefaultUniInteger))) (LamAbs () (Name [x64,x73] (Unique 3181)) (TyApp ()
  (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 3172)))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (TyInst () (Apply () (Apply () (TyInst ()
  (Apply () (TyInst () (Var () (Name
  [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 3177))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 3180))))
  (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 3182))) (Type ()) (TyApp
  () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 3172)))) (TyBuiltin
  () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x78,x27] (Unique
  3183)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 3184))) (Type ()) (TyInst () (Apply () (Apply ()
  (TyInst () (Apply () (TyInst () (Var () (Name
  [x4d,x61,x79,x62,x65,x5f,x6d,x61,x74,x63,x68] (Unique 3177))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))) (Var () (Name [x64,x73] (Unique 3181))))
  (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique 3185))) (Type ()) (TyApp
  () (TyVar () (TyName (Name [x4d,x61,x79,x62,x65] (Unique 3172)))) (TyBuiltin
  () (SomeTypeIn DefaultUniInteger))))) (LamAbs () (Name [x79,x27] (Unique
  3186)) (TyBuiltin () (SomeTypeIn DefaultUniInteger)) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 3187))) (Type ()) (Apply () (TyInst () (Var () (Name
  [x4a,x75,x73,x74] (Unique 3173))) (TyBuiltin () (SomeTypeIn
  DefaultUniInteger))) (Apply () (Apply () (Builtin () AddInteger) (Var () (Name
  [x78,x27] (Unique 3183)))) (Var () (Name [x79,x27] (Unique 3186)))))))) (TyAbs
  () (TyName (Name [x64,x65,x61,x64] (Unique 3188))) (Type ()) (TyInst () (Var
  () (Name [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 3175))) (TyBuiltin ()
  (SomeTypeIn DefaultUniInteger))))) (TyForall () (TyName (Name
  [x64,x65,x61,x64] (Unique 3189))) (Type ()) (TyVar () (TyName (Name
  [x64,x65,x61,x64] (Unique 3189))))))))) (TyAbs () (TyName (Name
  [x64,x65,x61,x64] (Unique 3190))) (Type ()) (TyInst () (Var () (Name
  [x4e,x6f,x74,x68,x69,x6e,x67] (Unique 3175))) (TyBuiltin () (SomeTypeIn
  DefaultUniInteger))))) (TyForall () (TyName (Name [x64,x65,x61,x64] (Unique
  3191))) (Type ()) (TyVar () (TyName (Name [x64,x65,x61,x64] (Unique
  3191)))))))))))) (TyLam () (TyName (Name [x61] (Unique 3192))) (Type ())
  (TySOP () [[TyVar () (TyName (Name [x61] (Unique 3192)))],[]]))) (TyAbs ()
  (TyName (Name [x61] (Unique 3193))) (Type ()) (LamAbs () (Name
  [x61,x72,x67,x5f,x30] (Unique 3194)) (TyVar () (TyName (Name [x61] (Unique
  3193)))) (Constr () (TySOP () [[TyVar () (TyName (Name [x61] (Unique
  3193)))],[]]) 0 [Var () (Name [x61,x72,x67,x5f,x30] (Unique 3194))])))) (TyAbs
  () (TyName (Name [x61] (Unique 3195))) (Type ()) (Constr () (TySOP () [[TyVar
  () (TyName (Name [x61] (Unique 3195)))],[]]) 1 []))) (TyAbs () (TyName (Name
  [x61] (Unique 3196))) (Type ()) (LamAbs () (Name [x78] (Unique 3197)) (TyApp
  () (TyLam () (TyName (Name [x61] (Unique 3198))) (Type ()) (TySOP () [[TyVar
  () (TyName (Name [x61] (Unique 3198)))],[]])) (TyVar () (TyName (Name [x61]
  (Unique 3196))))) (TyAbs () (TyName (Name
  [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3199))) (Type ()) (LamAbs ()
  (Name [x63,x61,x73,x65,x5f,x4a,x75,x73,x74] (Unique 3200)) (TyFun () (TyVar ()
  (TyName (Name [x61] (Unique 3196)))) (TyVar () (TyName (Name
  [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3199))))) (LamAbs () (Name
  [x63,x61,x73,x65,x5f,x4e,x6f,x74,x68,x69,x6e,x67] (Unique 3201)) (TyVar ()
  (TyName (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3199)))) (Case ()
  (TyVar () (TyName (Name [x6f,x75,x74,x5f,x4d,x61,x79,x62,x65] (Unique 3199))))
  (Var () (Name [x78] (Unique 3197))) [Var () (Name
  [x63,x61,x73,x65,x5f,x4a,x75,x73,x74] (Unique 3200)),Var () (Name
  [x63,x61,x73,x65,x5f,x4e,x6f,x74,x68,x69,x6e,x67] (Unique 3201))]))))))
.
