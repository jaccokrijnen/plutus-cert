|    TRANSFORMATION    | TRANSLATION RELATION                     |  PRE          | POST        | DECISION PROCEDURE           |  SEMANTIC PRESERVATION |
|----------------------|------------------------------------------|---------------|-------------|------------------------------|-------------------------
|Inline                |   TyInst case                            | global uniq   |             | bool, option, fuel -> ...    |                        |
|FloatLet              | … LetMerge is not optional, perhaps fine |               |             | … tactics                    |                        |
|DeadCode              | … use well-scoped, ty β-redex            | unique t      |             | Mostly commented out         | … WIP                  |
|Rename                | ✓ rename                                 |               | unique      |                              |                        |
|ThunkRecursions       | ✓ thunk_rec                              |               | _ -> _ type |                              |                        |
|Beta                  | ✓ extract_bindings                       |               |             |                              |                        |
|RecSplit              | ✓ split_rec (todo: use well-scoped)      |               |             |                              |                        |
|Unwrap                | ✓ unwrap_cancel                          |               |             |                              |                        |
|LetTypes              | ⋯                                        |               |             |                              |                        |
|Scott Enc             | … mostly commented out                   |               |             | … eq_refl (Term_eqb)         |                        |
|Let Rec               |                                          | _ -> _ type   | no letrec   |                              |                        |
|Desugar Let  (CNR)    | ✓ CNR (todo: make non-optional?)         |               |             | … bool, proof commented out  | … Dynamic              |
|LetNonStrict          | ✓ let_non_strict                         |               |             |                              |                        |


