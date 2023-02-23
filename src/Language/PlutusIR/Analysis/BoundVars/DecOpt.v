From PlutusCert Require Import 
  Util.In
  Util.List
  Util.DecOpt
  Language.PlutusIR
  Language.PlutusIR.Analysis.BoundVars.

From QuickChick Require Import QuickChick.



(* appears_bound_in_ty *)

QCDerive DecOpt for (appears_bound_in_ty x ty).

Instance DecOptappears_bound_in_ty_sound x ty: DecOptSoundPos (appears_bound_in_ty x ty).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_bound_in_ty_sound". Admitted.

Instance DecOptappears_bound_in_ty_complete x ty: DecOptCompletePos (appears_bound_in_ty x ty).
Proof. (* derive_complete. Qed. *) idtac "Admitted: DecOptappears_bound_in_ty_complete". Admitted.

Instance DecOptappears_bound_in_ty_mono x ty: DecOptSizeMonotonic (appears_bound_in_ty x ty).
Proof. (* derive_mon. Qed. *) idtac "Admitted: DecOptappears_bound_in_ty_mon". Admitted.



(* appears_bound_in_tm *)

QCDerive DecOpt for (appears_bound_in_tm x tm).

Instance DecOptappears_bound_in_tm_sound x tm: DecOptSoundPos (appears_bound_in_tm x tm).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_bound_in_tm_sound". Admitted.

Instance DecOptappears_bound_in_tm_complete x tm: DecOptCompletePos (appears_bound_in_tm x tm).
Proof. (* derive_complete. Qed. *) idtac "Admitted: DecOptappears_bound_in_tm_complete". Admitted.

Instance DecOptappears_bound_in_tm_mon x tm: DecOptSizeMonotonic (appears_bound_in_tm x tm).
Proof. (* derive_mon. Qed. *) idtac "Admitted: DecOptappears_bound_in_tm_mon". Admitted.


(* appears_bound_in_ann *)

QCDerive DecOpt for (appears_bound_in_ann x ann).

Instance DecOptappears_bound_in_ann_sound x ann: DecOptSoundPos (appears_bound_in_ann x ann).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_bound_in_ann_sound". Admitted.

Instance DecOptappears_bound_in_ann_complete x ann: DecOptCompletePos (appears_bound_in_ann x ann).
Proof. (* derive_complete. Qed. *) idtac "Admitted: DecOptappears_bound_in_ann_complete". Admitted.

Instance DecOptappears_bound_in_ann_mon x ann: DecOptSizeMonotonic (appears_bound_in_ann x ann).
Proof. (* derive_mon. Qed. *) idtac "Admitted: DecOptappears_bound_in_ann_mon". Admitted.
