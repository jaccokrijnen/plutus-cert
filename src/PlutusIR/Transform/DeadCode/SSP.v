Require Import PlutusCert.PlutusIR.
Import NamedTerm.
Require Import PlutusCert.PlutusIR.Transform.DeadCode2.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PlutusCert.PlutusIR.Semantics.Static.



Definition P_has_type Δ Γ t1 T : Prop :=
  forall t2,
    dc t1 t2 ->
    Δ ,, Γ |-+ t2 : T.

Definition P_constructor_well_formed Δ c T : Prop :=
  Δ |-ok_c c : T.

Definition P_bindings_well_formed_nonrec Δ Γ bs1 : Prop :=
  (
    forall bs2,
      Δ ,, Γ |-oks_nr bs1 ->
      Compat.Compat_Bindings dc bs1 bs2 ->
      Δ ,, Γ |-oks_nr bs2 /\
      map binds_Delta bs2 = map binds_Delta bs1 /\
      map binds_Gamma bs2 = map binds_Gamma bs1
  ).

Definition P_bindings_well_formed_rec Δ Γ bs1 : Prop :=
  forall bs2,
    Δ ,, Γ |-oks_r bs1 ->
    Compat.Compat_Bindings dc bs1 bs2 ->
    Δ ,, Γ |-oks_r bs2 /\
    map binds_Delta bs2 = map binds_Delta bs1 /\
    map binds_Gamma bs2 = map binds_Gamma bs1.

Definition P_binding_well_formed Δ Γ b1 : Prop :=
  (
    forall b2,
      Δ ,, Γ |-ok_b b1 ->
      Compat.Compat_Binding dc b1 b2 ->
      Δ ,, Γ |-ok_b b2 /\
      binds_Delta b2 = binds_Delta b1 /\
      binds_Gamma b2 = binds_Gamma b1
  ).

#[export] Hint Unfold
  P_has_type
  P_constructor_well_formed
  P_bindings_well_formed_nonrec
  P_bindings_well_formed_rec
  P_binding_well_formed
  : core.

Theorem dc__SSP : forall Δ Γ t1 T,
    Δ ,, Γ |-+ t1 : T ->
    P_has_type Δ Γ t1 T.
Proof with (eauto with typing).
Admitted.
