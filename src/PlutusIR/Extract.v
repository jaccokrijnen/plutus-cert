From PlutusCert Require Import DeadCode.DecideBool.


From Coq Require Import Extraction.
Require Import Strings.Ascii.
Extraction Language Haskell.
Extraction "hs-src/PlutusIR/Certifier/Extracted.hs"
  dec_Term
  (* dec_unique *)
  (* ascii_of_nat *)
.
