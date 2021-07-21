
- define built-in types and terms

(hs)
|
| desugar
|
GHC.CoreExpr (desugared before optimization)
|
| reordering of top-level definitions
| adds top-level annotations
| some local inlining
| "case .. of wild_00" => "case .. of"
| ???
|
GHC.CoreExpr (desugared after optimization)
|
| simplifier let out-floating (Seems to depend on annotations) + ???
| (no changes observed to embedded plutus code)
| side-effect: ensure unfoldings are present
|
GHC.CoreExpr (after simplifier)
|
| add built-ins and compileExpr (include thunking, scott, wildcards for case)
| ????
|
PIRTerm
|
| removes dead bindings (mostly builtins, but also a "wild" which was probably introduced to reference to the scrutinee of a case)
| (see PlutusIR.Compiler.compileToReadable)
|
PIRTerm
|
| eliminate let-bindings (let-desugar, scott-encoding)
|
PLC
