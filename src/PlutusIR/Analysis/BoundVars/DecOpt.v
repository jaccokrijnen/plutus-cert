From PlutusCert Require Import 
  Util.List
  PlutusIR
  PlutusIR.Analysis.BoundVars.
From QuickChick Require Import QuickChick.



(* appears_bound_in_ty *)

QCDerive DecOpt for (appears_bound_in_ty x ty).

Instance appears_bound_in_ty_DecOpt_sound x ty: DecOptSoundPos (appears_bound_in_ty x ty).
Proof. (* derive_sound. Qed. *) idtac "Admitted: appears_bound_in_ty_DecOpt_sound". Admitted.

Instance appears_bound_in_ty_DecOpt_complete x ty: DecOptCompletePos (appears_bound_in_ty x ty).
Proof. (* derive_complete. Qed. *) idtac "Admitted: appears_bound_in_ty_DecOpt_complete". Admitted.

Instance appears_bound_in_ty_DecOpt_mono x ty: DecOptSizeMonotonic (appears_bound_in_ty x ty).
Proof. (* derive_mon. Qed. *) idtac "Admitted: appears_bound_in_ty_DecOpt_mon". Admitted.




(* appears_bound_in_tm *)

QCDerive DecOpt for (appears_bound_in_tm x tm).

Instance appears_bound_in_tm_DecOpt_sound x tm: DecOptSoundPos (appears_bound_in_tm x tm).
Proof. (* derive_sound. Qed. *) idtac "Admitted: appears_bound_in_tm_DecOpt_sound". Admitted.

Instance appears_bound_in_tm_DecOpt_complete x tm: DecOptCompletePos (appears_bound_in_tm x tm).
Proof. (* derive_complete. Qed. *) idtac "Admitted: appears_bound_in_tm_DecOpt_complete". Admitted.

Instance appears_bound_in_tm_DecOpt_mon x tm: DecOptSizeMonotonic (appears_bound_in_tm x tm).
Proof. (* derive_mon. Qed. *) idtac "Admitted: appears_bound_in_tm_DecOpt_mon". Admitted.



(* appears_bound_in_ann *)

QCDerive DecOpt for (appears_bound_in_ann x ann).

Instance appears_bound_in_ann_DecOpt_sound x ann: DecOptSoundPos (appears_bound_in_ann x ann).
Proof. (* derive_sound. Qed. *) idtac "Admitted: appears_bound_in_ann_DecOpt_sound". Admitted.

Instance appears_bound_in_ann_DecOpt_complete x ann: DecOptCompletePos (appears_bound_in_ann x ann).
Proof. (* derive_complete. Qed. *) idtac "Admitted: appears_bound_in_ann_DecOpt_complete". Admitted.

Instance appears_bound_in_ann_DecOpt_mon x ann: DecOptSizeMonotonic (appears_bound_in_ann x ann).
Proof. (* derive_mon. Qed. *) idtac "Admitted: appears_bound_in_ann_DecOpt_mon". Admitted.
