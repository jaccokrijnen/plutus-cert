From PlutusIR Require Import
  Cert.Relation.
  Cert.Dump1
.

Fail Check (dec_correct let_nonrec Dump1.term Dump1.term eq_refl).

From PlutusCert Require TimelockDumps.

Check (dec_correct let_nonrec TimelockDumps.plc_4_inlined TimelockDumps.plc_5_compileNonRecTerms eq_refl).
