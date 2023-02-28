From PlutusCert Require Import
  Util
  Util.List
  Util.In
  Language.PlutusIR.Analysis.Equality.DecOpt
  Language.PlutusIR.

From Coq Require Import
  Lists.List
  Arith.PeanoNat.

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

Ltac derive__complete HComplete :=
  unfold DecOptCompletePos;
  unfold decOpt;
  intros H;
  apply complete;
  apply HComplete;
  assumption.


(* Ltac and helper lemmas for deriving negated soundness proofs for In istances *)

Lemma match_contr : forall x,
  match x with
  | Just true => Just true
  | _ => None
  end = Just false -> False.
Proof. intro. destruct x; intro H; try destruct b; inversion H. Qed.

Lemma match_destruct_false : forall b,
  match b with
  | Some true => Some true
  | Some false => Some false
  | None => None
  end = Just false <-> b = Some false.
Proof. destruct b; split; intros; try destruct b; inversion H; reflexivity. Qed.


Ltac derive_in_complete_neg :=
  intros x xs;
  unfold DecOptCompleteNeg;
  intros HNin;
  unfold decOpt;
  remember (List.length xs + 1) as s eqn:Hs;
  exists s;
  simpl_minus_methods;
  generalize &s at 1 as s';
  revert x xs HNin Hs;
  induction s as [| s IHs]; intros x xs HNin Hs s'; unfold checker_backtrack; 
  [ destruct xs; inversion Hs
  | destruct xs as [| x' xs'];
    [ reflexivity
    | unfold decOpt in *; unfold dec_decOpt in *; unfold dec in *; unfold Eq__Dec in *;
      destruct (dec_eq x x') as [Heq | HNeq]; destruct (dec_eq x' x) as [Heq' | HNeq']; subst;
      [ exfalso; apply HNin; constructor
      | reflexivity
      | exfalso; apply HNeq; reflexivity
      | repeat apply <- match_destruct_false;
        apply IHs;
        [ intro HNin'; apply HNin; constructor; assumption
        | simpl in Hs; apply eq_add_S in Hs; assumption
        ]
      ]
    ]
  ].

QCDerive EnumSized for ascii.
QCDerive EnumSized for string.



QCDerive DecOpt for (NameIn x xs).

Instance DecOptNameIn_sound x xs : DecOptSoundPos (NameIn x xs).
Proof. derive_sound. Qed.

Instance DecOptNameIn_complete x xs : DecOptCompletePos (NameIn x xs).
Proof. derive_complete. Qed.

Instance DecOptNameIn_mon x xs : DecOptSizeMonotonic (NameIn x xs).
Proof. derive_mon. Qed.

Instance DecOptNameIn_complete_neg x xs : DecOptCompleteNeg (NameIn x xs).
Proof. revert x xs. derive_in_complete_neg. Qed.
  


QCDerive DecOpt for (TyIn x xs).

Instance DecOptTyIn_sound x xs : DecOptSoundPos (TyIn x xs).
Proof. derive_sound. Qed.

Instance DecOptTyIn_complete x xs : DecOptCompletePos (TyIn x xs).
Proof. derive_complete. Qed.

Instance DecOptTyIn_mon x xs : DecOptSizeMonotonic (TyIn x xs).
Proof. derive_mon. Qed.

Instance DecOptTyIn_complete_neg x xs : DecOptCompleteNeg (TyIn x xs).
Proof. revert x xs. derive_in_complete_neg. Qed.



QCDerive DecOpt for (ConstrIn x xs).

Instance DecOptConstrIn_sound x xs : DecOptSoundPos (ConstrIn x xs).
Proof. derive_sound. Qed.

Instance DecOptConstrIn_complete x xs : DecOptCompletePos (ConstrIn x xs).
Proof. derive_complete. Qed.

Instance DecOptConstrIn_mon x xs : DecOptSizeMonotonic (ConstrIn x xs).
Proof. derive_mon. Qed.

Instance DecOptConstrIn_complete_neg x xs : DecOptCompleteNeg (ConstrIn x xs).
Proof. revert x xs. derive_in_complete_neg. Qed.




(* NOTE: Derives an instance that requires an Enum instance over its 2 type arguments,
    even though the instance are not used in the computation *)
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
