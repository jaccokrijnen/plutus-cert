From PlutusCert Require Import
  Util.DecOpt
  Util
  Language.PlutusIR
  Language.PlutusIR.Semantics.Dynamic.Values
  Language.PlutusIR.Semantics.Dynamic.BuiltinMeanings.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.



(* derivation of proxy type and soundness proof *)
MetaCoq Run (deriveCTProxy value).

Theorem value_proxy_sound : value_proxy_sound_type.
Proof. deriveCTProxy_sound core. Qed.



QCDerive DecOpt for (is_error tm).

Instance DecOptis_error_sound tm: DecOptSoundPos (is_error tm).
Proof. derive_sound. Qed.

Instance DecOptis_error_complete tm: DecOptCompletePos (is_error tm).
Proof. derive_complete. Qed.

Instance DecOptis_error_mon tm: DecOptSizeMonotonic (is_error tm).
Proof. derive_mon. Qed.



QCDerive DecOpt for (value_proxy tag).

Instance DecOptvalue_proxy_sound tag : DecOptSoundPos (value_proxy tag).
Proof. derive_sound. Qed.



(* value *)

Instance DecOptvalue tm : DecOpt (value tm) :=
{| decOpt s := @decOpt (value_proxy (value_tag tm)) (DecOptvalue_proxy (value_tag tm)) s |}.

Instance DecOptvalue_sound tm : DecOptSoundPos (value tm).
Proof. derive__sound (value_proxy_sound (value_tag tm)). Qed.



(* neutral_value *)

Instance DecOptneutral_value n tm : DecOpt (neutral_value n tm) :=
{| decOpt s := @decOpt (value_proxy (neutral_value_tag n tm)) (DecOptvalue_proxy (neutral_value_tag n tm)) s |}.

Instance DecOptneutral_value_sound n tm : DecOptSoundPos (neutral_value n tm).
Proof. derive__sound (value_proxy_sound (neutral_value_tag n tm)). Qed.





QCDerive DecOpt for (fully_applied_neutral n tm).

Instance DecOptfully_applied_neutral_sound n tm : DecOptSoundPos (fully_applied_neutral n tm).
Proof. derive_sound. Qed.

