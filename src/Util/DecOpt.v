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

Instance DecOptNameIn_sound x xs : DecOptSoundPos (NameIn x xs).
Proof. derive_sound. Qed.

Instance DecOptNameIn_complete x xs : DecOptCompletePos (NameIn x xs).
Proof. derive_complete. Qed.

Instance DecOptNameIn_mon x xs : DecOptSizeMonotonic (NameIn x xs).
Proof. derive_mon. Qed.



QCDerive DecOpt for (Lookup k v kvs).

(* NOTE: if the type arguments, and its requirements are not added in this definition, 
    QuickChick will still be able to derive a soundness proof, but specifically for
    an instance of Lookup with the type string for the type arguments A and B *)
Instance DecOptLookup_sound 
  (* Type arguments *)
  {A B : Type} 

  (* Requirements for ploymorphic DecOptLookup instance *)
  {Dec_Eq_A : Dec_Eq A} {Dec_Eq_B : Dec_Eq B}
  {Enum_A : Enum A}  {Enum_B : Enum B} 

  (* Actual arguments *)
  (k : A) (v : B) (kvs : list (A * B)) : DecOptSoundPos (Lookup k v kvs).
Proof. derive_sound. Qed.

Instance DecOptLookup_complete
  {A B : Type} 
  {Dec_Eq_A : Dec_Eq A} {Dec_Eq_B : Dec_Eq B}
  {Enum_A : Enum A}  {Enum_B : Enum B} 
  (k : A) (v : B) (kvs : list (A * B)) : DecOptCompletePos (Lookup k v kvs).
Proof. derive_complete. Qed.

Instance DecOptLookup_monotonic
  {A B : Type} 
  {Dec_Eq_A : Dec_Eq A} {Dec_Eq_B : Dec_Eq B}
  {Enum_A : Enum A}  {Enum_B : Enum B} 
  (k : A) (v : B) (kvs : list (A * B)) : DecOptSizeMonotonic (Lookup k v kvs).
Proof. derive_mon. Qed.



QCDerive DecOpt for (lt_nat n m).

Instance DecOptlt_nat_sound n m: DecOptSoundPos (lt_nat n m).
Proof. derive_sound. Qed.

Instance DecOptlt_nat_complete n m: DecOptCompletePos (lt_nat n m).
Proof. derive_complete. Qed.

Instance DecOptlt_nat_monotonic n m: DecOptSizeMonotonic (lt_nat n m).
Proof. derive_mon. Qed.




Instance DecOptle n m : DecOpt (le n m) :=
  {| decOpt _ := Some (Nat.leb n m) |}.

Instance DecOptle_sound n m : DecOptSoundPos (le n m).
Proof.
  unfold DecOptSoundPos.
  intros.
  injection H as H.
  apply Nat.leb_le.
  apply H.
Qed.
