From PlutusCert Require Import
  Util
  Util.List.

From Coq Require Import Arith.PeanoNat.

From QuickChick Require Import QuickChick.



(* Ltac for deriving the several DecOpt soundness proofs for some proxy 
    in terms of the mutual inductive relations it was derived over*)
Ltac derive__sound HSound :=
  unfold DecOptSoundPos;
  unfold decOpt;
  intros s H;
  apply HSound;
  apply sound in H;
  assumption.





QCDerive EnumSized for ascii.
QCDerive EnumSized for string.



QCDerive DecOpt for (NameIn x xs).

Instance NameIn_DecOpt_sound x xs : DecOptSoundPos (NameIn x xs).
Proof. derive_sound. Qed.

Instance NameIn_DecOpt_complete x xs : DecOptCompletePos (NameIn x xs).
Proof. derive_complete. Qed.

Instance NameIn_DecOpt_monotonic x xs : DecOptSizeMonotonic (NameIn x xs).
Proof. derive_mon. Qed.



QCDerive DecOpt for (lt_nat n m).

Instance lt_nat_DecOpt_sound n m: DecOptSoundPos (lt_nat n m).
Proof. derive_sound. Qed.

Instance lt_nat_DecOpt_complete n m: DecOptCompletePos (lt_nat n m).
Proof. derive_complete. Qed.

Instance lt_nat_DecOpt_monotonic n m: DecOptSizeMonotonic (lt_nat n m).
Proof. derive_mon. Qed.



Instance DecOptlt n m : DecOpt (le n m) :=
  {| decOpt _ := Some (Nat.leb n m) |}.

Instance DecOptlt_sound n m : DecOptSoundPos (lt n m).
Proof.
  unfold DecOptSoundPos.
  intros.
  injection H as H.
  apply Nat.leb_le.
  apply H.
Qed.

