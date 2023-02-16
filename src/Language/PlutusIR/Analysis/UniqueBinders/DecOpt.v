From PlutusCert Require Import 
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Analysis.BoundVars
  Language.PlutusIR.Analysis.BoundVars.DecOpt
  Language.PlutusIR.Analysis.UniqueBinders.

From QuickChick Require Import QuickChick.



QCDerive DecOpt for (unique_ty ty).

Instance DecOptunique_ty_sound ty: DecOptSoundPos (unique_ty ty).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptunique_ty_sound". Admitted.

(*
Instance unique_ty_DecOpt_complete ty: DecOptCompletePos (unique_ty ty).
Proof. (* derive_complete. Qed. *) idtac "Admitted: unique_ty_DecOpt_complete". Admitted.

Instance unique_ty_DecOpt_mono ty: DecOptSizeMonotonic (unique_ty ty).
Proof. (* derive_mon. Qed. *) idtac "Admitted: unique_ty_DecOpt_mon". Admitted.
 *)





QCDerive DecOpt for (unique_tm ty).

Instance DecOptunique_tm_sound tm: DecOptSoundPos (unique_tm tm).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptunique_tm_sound". Admitted.

(*
Instance unique_tm_DecOpt_complete tm: DecOptCompletePos (unique_tm tm).
Proof. (* derive_complete. Qed. *) idtac "Admitted: unique_tm_DecOpt_complete". Admitted.

Instance unique_tm_DecOpt_mono tm: DecOptSizeMonotonic (unique_tm tm).
Proof. (* derive_mon. Qed. *) idtac "Admitted: unique_tm_DecOpt_mon". Admitted.
 *)
