From PlutusCert Require Import
  Util.List
  Util.DecOpt
  Language.PlutusIR
  (* Language.PlutusIR.DecOpt *)
  (* Language.PlutusIR.Analysis.Equality.DecOpt *)
  Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI
  Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.DecOpt
  Language.PlutusIR.Transform.Rename.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.



QCDerive DecOpt for (no_capture x t Γ).

Instance DecOptno_capture_sound x t Γ : DecOptSoundPos (no_capture x t Γ).
Proof. derive_sound. Qed.



QCDerive DecOpt for (no_captureA α t Δ).

Instance DecOptno_captureA_sound α t Δ : DecOptSoundPos (no_capture α t Δ).
Proof. derive_sound. Qed.



QCDerive DecOpt for (no_ty_capture α τ Δ).

Instance DecOptno_ty_capture_sound α τ Δ : DecOptSoundPos (no_ty_capture α τ Δ).
Proof. derive_sound. Qed.



QCDerive DecOpt for (no_ty_capture_constructors α cs Δ).  

Instance DecOptno_ty_capture_constructors_sound α cs Δ : DecOptSoundPos (no_ty_capture_constructors α cs Δ).
Proof. derive_sound. Qed.



QCDerive DecOpt for (rename_tvs Δ cs tvs tvs' Δ_tvs).

Instance DecOptrename_tvs_sound Δ cs tvs tvs' Δ_tvs : DecOptSoundPos (rename_tvs Δ cs tvs tvs' Δ_tvs).
Proof. derive_sound. Qed.



QCDerive DecOpt for (rename_ty Δ ty ty').

Instance DecOptrename_ty_sound Δ ty ty': DecOptSoundPos (rename_ty Δ ty ty').
Proof. derive_sound. Qed.




MetaCoq Run (deriveCTProxy rename).

Local Hint Constructors rename rename_binding rename_Bindings_Rec rename_constrs : rename_hints. 

Lemma rename_proxy_sound : rename_proxy_sound_type.
Proof. deriveCTProxy_sound rename_hints. Qed.

 


QCDerive DecOpt for (rename_proxy Γ Δ tm tm').

