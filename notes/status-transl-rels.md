|    TRANSFORMATION    | TRANSLATION RELATION                     |  PRE          | POST        | DECISION PROCEDURE           |  SEMANTIC PRESERVATION |
|----------------------|------------------------------------------|---------------|-------------|------------------------------|-------------------------
|Inline                | ✓ `inline`                               | unique        |             | bool, option, fuel -> ...    |                        |
|FloatLet              | ✓ `let_float` \*                         |               |             | … tactics                    |                        |
|DeadCode              | ✓ `dead_code` \*                         | unique        |             | Mostly commented out         | … WIP                  |
|Rename                | ✓ `rename`                               |               | unique      |                              |                        |
|ThunkRecursions       | ✓ `thunk_rec`                            |               | _ -> _ type |                              |                        |
|Beta                  | ✓ `extract_bindings`                     |               |             |                              |                        |
|RecSplit              | ✓ `split_rec` \*                         |               |             |                              |                        |
|Unwrap                | ✓ `unwrap_cancel`                        |               |             |                              |                        |
|LetTypes              | ✓ `ty_let`                               |               | no let type |                              |                        |
|Scott Enc             | …                                        |               | no let data | … eq_refl (Term_eqb)         |                        |
|Let Rec               | …                                        | _ -> _ type   | no let rec  |                              |                        |
|Desugar Let  (CNR)    | ✓ `CNR`                                  |               | no let term | … bool, proof commented out  | … Dynamic              |
|LetNonStrict          | ✓ `let_non_strict`                       |               |             |                              |                        |


\* : use well-scoped
