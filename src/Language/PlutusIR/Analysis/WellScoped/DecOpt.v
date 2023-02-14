From PlutusCert Require Import
  Util.List
  Language.PlutusIR
  Language.PlutusIR.Analysis.WellScoped.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.




QCDerive DecOpt for (well_scoped_Ty Δ Ty).

Instance DecOptwell_scoped_Ty_sound Δ ty: DecOptSoundPos (well_scoped_Ty Δ ty).
Proof. derive_sound. Qed.



QCDerive DecOpt for (constructors_well_formed Δ c).

Instance DecOptconstructors_well_formed_sound Δ c : DecOptSoundPos (constructors_well_formed Δ c).
Proof. derive_sound. Qed.



(* derivation of proxy type and soundness proof *)
MetaCoq Run (deriveCTProxy well_scoped).

Theorem well_scoped_proxy_sound : well_scoped_proxy_sound_type.
Proof. deriveCTProxy_sound well_scoped_hints. Qed.



QCDerive DecOpt for (well_scoped_proxy tag).

Instance DecOptwell_scoped_proxy_sound tag : DecOptSoundPos (well_scoped_proxy tag).
Proof. derive_sound. Qed.



(* helper Ltac (is generic, still needs to be given a place) *)
Ltac derive__sound HSound :=
  unfold DecOptSoundPos;
  unfold decOpt;
  intros s H;
  apply HSound;
  apply sound in H;
  assumption.



(* well_scoped *)

Instance DecOptwell_scoped c1 c2 tm : DecOpt (well_scoped c1 c2 tm) :=
{| decOpt s := @decOpt (well_scoped_proxy (well_scoped_tag c1 c2 tm)) (DecOptwell_scoped_proxy (well_scoped_tag c1 c2 tm)) s |}.

Instance DecOptwell_scoped_sound c1 c2 tm : DecOptSoundPos (well_scoped c1 c2 tm).
Proof. derive__sound (well_scoped_proxy_sound (well_scoped_tag c1 c2 tm)). Qed.



(* bindings_well_formed_nonrec *)

Instance DecOptbindings_well_formed_nonrec c1 c2 bs : DecOpt (bindings_well_formed_nonrec c1 c2 bs) :=
{| decOpt s := @decOpt (well_scoped_proxy (bindings_well_formed_nonrec_tag c1 c2 bs)) (DecOptwell_scoped_proxy (bindings_well_formed_nonrec_tag c1 c2 bs)) s |}.

Instance DecOptbindings_bindings_well_formed_nonrec c1 c2 bs : DecOptSoundPos (bindings_well_formed_nonrec c1 c2 bs).
Proof. derive__sound (well_scoped_proxy_sound (bindings_well_formed_nonrec_tag c1 c2 bs)). Qed.



(* bindings_well_formed_rec *)

Instance DecOptbindings_well_formed_rec c1 c2 bs : DecOpt (bindings_well_formed_rec c1 c2 bs) :=
{| decOpt s := @decOpt (well_scoped_proxy (bindings_well_formed_rec_tag c1 c2 bs)) (DecOptwell_scoped_proxy (bindings_well_formed_rec_tag c1 c2 bs)) s |}.

Instance DecOptbindings_bindings_well_formed_rec c1 c2 bs : DecOptSoundPos (bindings_well_formed_rec c1 c2 bs).
Proof. derive__sound (well_scoped_proxy_sound (bindings_well_formed_rec_tag c1 c2 bs)). Qed.



(* binding_well_formed *)

Instance DecOptbinding_well_formed c1 c2 bs : DecOpt (binding_well_formed c1 c2 bs) :=
{| decOpt s := @decOpt (well_scoped_proxy (binding_well_formed_tag c1 c2 bs)) (DecOptwell_scoped_proxy (binding_well_formed_tag c1 c2 bs)) s |}.

Instance DecOptbindings_binding_well_formed c1 c2 b : DecOptSoundPos (binding_well_formed c1 c2 b).
Proof. derive__sound (well_scoped_proxy_sound (binding_well_formed_tag c1 c2 b)). Qed.
