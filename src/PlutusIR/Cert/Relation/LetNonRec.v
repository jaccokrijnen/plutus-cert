From PlutusCert Require Import
  Cert.Relation.Types
  LetNonRec.Spec
  LetNonRec.DecideBool
  LetNonRec.DSP
.

Definition let_nonrec : rel_verified :=
  mk_rel_verified
    ( mk_rel_decidable
        CNR_Term
        dec_Term
        dec_Term_equiv
    )
    CNR_Term__sem
.
