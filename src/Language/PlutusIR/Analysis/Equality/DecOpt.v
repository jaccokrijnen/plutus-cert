From PlutusCert Require Import
  (*  Util.List
     Util.DecOpt *)
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality.

Import NamedTerm.

From QuickChick Require Import QuickChick.


Instance Dec_Eq_Ty: Dec_Eq Ty.
Proof. constructor. apply Ty_dec. Qed.

Instance Dec_Eq_Term : Dec_Eq Term.
Proof. constructor. apply Term_dec. Qed.
