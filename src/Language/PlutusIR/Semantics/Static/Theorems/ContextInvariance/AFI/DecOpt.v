From PlutusCert Require Import
  Util.In
  Util.DecOpt 
  Language.PlutusIR
  Language.PlutusIR.Analysis.BoundVars
  (*
  Language.PlutusIR.DecOpt
  Language.PlutusIR.Analysis.Equality.DecOpt
   *)
  Language.PlutusIR.Semantics.Static.Theorems.ContextInvariance.AFI.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.

Import NamedTerm.



QCDerive DecOpt for (appears_free_in_ty name ty).

Instance DecOptappears_free_in_ty_sound name ty: DecOptSoundPos (appears_free_in_ty name ty).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_free_in_ty_sound". Admitted.

Instance DecOptappears_free_in_ty_complete name ty: DecOptCompletePos (appears_free_in_ty name ty).
Proof. (* derive_complete. Qed. *) idtac "Admitted: DecOptappears_free_in_ty_sound". Admitted.

Instance DecOptappears_free_in_ty_mon name ty: DecOptSizeMonotonic (appears_free_in_ty name ty).
Proof. (* derive_mon. Qed. *) idtac "Admitted: DecOptappears_free_in_ty_mon". Admitted.






MetaCoq Run (deriveCTProxy appears_free_in_tm).

Lemma appears_free_in_tm_proxy_sound : appears_free_in_tm_proxy_sound_type.
Proof. deriveCTProxy_sound core. Qed.



QCDerive DecOpt for (appears_free_in_tm_proxy tag).

Instance DecOptappears_free_in_tm_proxy_sound tag : DecOptSoundPos (appears_free_in_tm_proxy tag).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_free_in_tm_proxy_sound". Admitted.


(* appears_free_in_tm *)

Instance DecOptappears_free_in_tm name tm : DecOpt (appears_free_in_tm name tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm_tag name tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm_tag name tm)) s |}.

Instance DecOptappears_free_in_tm_sound name tm : DecOptSoundPos (appears_free_in_tm name tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm_tag name tm)). Qed.



(* appears_free_in_tm__bindings_nonrec *)

Instance DecOptappears_free_in_tm__bindings_nonrec bs tm : DecOpt (appears_free_in_tm__bindings_nonrec bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__bindings_nonrec_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__bindings_nonrec_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__bindings_nonrec_sound bs tm : DecOptSoundPos (appears_free_in_tm__bindings_nonrec bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__bindings_nonrec_tag bs tm)). Qed.



(* appears_free_in_tm__bindings_rec *)

Instance DecOptappears_free_in_tm__bindings_rec bs tm : DecOpt (appears_free_in_tm__bindings_rec bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__bindings_rec_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__bindings_rec_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__bindings_rec_sound bs tm : DecOptSoundPos (appears_free_in_tm__bindings_rec bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__bindings_rec_tag bs tm)). Qed.


(* appears_free_in_tm__binding *)

Instance DecOptappears_free_in_tm__binding bs tm : DecOpt (appears_free_in_tm__binding bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__binding_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__binding_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__binding_sound bs tm : DecOptSoundPos (appears_free_in_tm__binding bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__binding_tag bs tm)). Qed.




MetaCoq Run (deriveCTProxy appears_free_in_ann).

Lemma appears_free_in_ann_proxy_sound : appears_free_in_ann_proxy_sound_type.
Proof. deriveCTProxy_sound core. Qed.

(*

QCDerive DecOpt for (appears_free_in_ann_proxy tag).

Instance DecOptappears_free_in_ann_proxy_sound tag : DecOptSoundPos (appears_free_in_ann_proxy tag).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptappears_free_in_ann_proxy_sound". Admitted.



(* appears_free_in_ann *)

Instance DecOptappears_free_in_ann name ann : DecOpt (appears_free_in_ann name ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann_tag name ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann_tag name ann)) s |}.

Instance DecOptappears_free_in_ann_sound name ann : DecOptSoundPos (appears_free_in_ann name ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann_tag name ann)). Qed.



(* appears_free_in_ann__bindings_nonrec *)

Instance DecOptappears_free_in_ann__bindings_nonrec bs ann : DecOpt (appears_free_in_ann__bindings_nonrec bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__bindings_nonrec_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__bindings_nonrec_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__bindings_nonrec_sound bs ann : DecOptSoundPos (appears_free_in_ann__bindings_nonrec bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__bindings_nonrec_tag bs ann)). Qed.



(* appears_free_in_ann__bindings_rec *)

Instance DecOptappears_free_in_ann__bindings_rec bs ann : DecOpt (appears_free_in_ann__bindings_rec bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__bindings_rec_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__bindings_rec_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__bindings_rec_sound bs ann : DecOptSoundPos (appears_free_in_ann__bindings_rec bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__bindings_rec_tag bs ann)). Qed.


(* appears_free_in_ann__binding *)

Instance DecOptappears_free_in_ann__binding bs ann : DecOpt (appears_free_in_ann__binding bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__binding_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__binding_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__binding_sound bs ann : DecOptSoundPos (appears_free_in_ann__binding bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__binding_tag bs ann)). Qed.

 *)
