From PlutusCert Require Import
  Util.List
  Util.DecOpt
  Language.PlutusIR
  Language.PlutusIR.DecOpt
  Language.PlutusIR.Analysis.Purity
  Language.PlutusIR.Semantics.Dynamic.Values
  Language.PlutusIR.Semantics.Dynamic.Values.DecOpt.

From QuickChick Require Import QuickChick.


(* Used in the purity relation *)
QCDerive EnumSized for binder_info.

Instance Decbinder_info : Dec_Eq binder_info.
Proof. dec_eq. Qed.



QCDerive DecOpt for (is_pure Γ tm).

Instance DecOptid_pure_sound Γ tm : DecOptSoundPos (is_pure Γ tm).
Proof. derive_sound. Qed.




QCDerive DecOpt for (pure_binding Γ tm).

Instance DecOptpure_binding_sound Γ tm : DecOptSoundPos (pure_binding Γ tm).
Proof. derive_sound. Qed.
