From PlutusCert Require Import
  Util.List
  Util.DecOpt
  Language.PlutusIR
  Language.PlutusIR.DecOpt
  Language.PlutusIR.Transform.InlineNonRec
  Language.PlutusIR.Analysis.Equality.DecOpt.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.




QCDerive EnumSized for binder_info.

Instance Dec_eq_binder_info : Dec_Eq binder_info.
Proof.
  constructor.
  unfold ssrbool.decidable.
  decide equality.
  - apply Dec_eq_Term.
  - apply Dec_eq_Ty.
Qed.

Instance Dec_eq_ctx : Dec_Eq ctx.
Proof.
  apply Dec_eq_list.
  apply Dec_eq_prod.
  - apply Dec_eq_string.
  - apply Dec_eq_binder_info.
Qed.







MetaCoq Run (deriveCTProxy inline_nonrec).

Local Hint Constructors 
  inline_nonrec 
  inline_nonrec_Bindings_Rec 
  inline_nonrec_Bindings_NonRec 
  inline_nonrec_Binding 
  inline_nonrec_Ty 
    : inline_nonrec_hints. 

Lemma inline_nonrec_proxy_sound : inline_nonrec_proxy_sound_type.
Proof. deriveCTProxy_sound inline_nonrec_hints. Qed.





QCDerive DecOpt for (inline_nonrec_proxy tag).

Instance DecOptinline_nonrec_proxy_sound tag : DecOptSoundPos (inline_nonrec_proxy tag).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptinline_nonrec_proxy_sound". Admitted.



(* inline_nonrec *)

Instance DecOptinline_nonrec c1 c2 tm : DecOpt (inline_nonrec c1 c2 tm) :=
{| decOpt s := @decOpt (inline_nonrec_proxy (inline_nonrec_tag c1 c2 tm)) (DecOptinline_nonrec_proxy (inline_nonrec_tag c1 c2 tm)) s |}.

Instance DecOptinline_nonrec_sound c1 c2 tm : DecOptSoundPos (inline_nonrec c1 c2 tm).
Proof. derive__sound (inline_nonrec_proxy_sound (inline_nonrec_tag c1 c2 tm)). Qed.



(* inline_nonrec_Bindings_Rec *)

Instance DecOptinline_nonrec_Bindings_Rec c1 c2 tm : DecOpt (inline_nonrec_Bindings_Rec c1 c2 tm) :=
{| decOpt s := @decOpt (inline_nonrec_proxy (inline_nonrec_Bindings_Rec_tag c1 c2 tm)) (DecOptinline_nonrec_proxy (inline_nonrec_Bindings_Rec_tag c1 c2 tm)) s |}.

Instance DecOptinline_nonrec_Bindings_Rec_sound c1 c2 tm : DecOptSoundPos (inline_nonrec_Bindings_Rec c1 c2 tm).
Proof. derive__sound (inline_nonrec_proxy_sound (inline_nonrec_Bindings_Rec_tag c1 c2 tm)). Qed.



(* inline_nonrec_Bindings_NonRec *)

Instance DecOptinline_nonrec_Bindings_NonRec c1 c2 tm : DecOpt (inline_nonrec_Bindings_NonRec c1 c2 tm) :=
{| decOpt s := @decOpt (inline_nonrec_proxy (inline_nonrec_Bindings_NonRec_tag c1 c2 tm)) (DecOptinline_nonrec_proxy (inline_nonrec_Bindings_NonRec_tag c1 c2 tm)) s |}.

Instance DecOptinline_nonrec_Bindings_NonRec_sound c1 c2 tm : DecOptSoundPos (inline_nonrec_Bindings_NonRec c1 c2 tm).
Proof. derive__sound (inline_nonrec_proxy_sound (inline_nonrec_Bindings_NonRec_tag c1 c2 tm)). Qed.



(* inline_nonrec_Binding *)

Instance DecOptinline_nonrec_Binding c1 c2 tm : DecOpt (inline_nonrec_Binding c1 c2 tm) :=
{| decOpt s := @decOpt (inline_nonrec_proxy (inline_nonrec_Binding_tag c1 c2 tm)) (DecOptinline_nonrec_proxy (inline_nonrec_Binding_tag c1 c2 tm)) s |}.

Instance DecOptinline_nonrec_Binding_sound c1 c2 tm : DecOptSoundPos (inline_nonrec_Binding c1 c2 tm).
Proof. derive__sound (inline_nonrec_proxy_sound (inline_nonrec_Binding_tag c1 c2 tm)). Qed.



(* inline_nonrec_Ty *)

Instance DecOptinline_nonrec_Ty c1 c2 tm : DecOpt (inline_nonrec_Ty c1 c2 tm) :=
{| decOpt s := @decOpt (inline_nonrec_proxy (inline_nonrec_Ty_tag c1 c2 tm)) (DecOptinline_nonrec_proxy (inline_nonrec_Ty_tag c1 c2 tm)) s |}.

Instance DecOptinline_nonrec_Ty_sound c1 c2 tm : DecOptSoundPos (inline_nonrec_Ty c1 c2 tm).
Proof. derive__sound (inline_nonrec_proxy_sound (inline_nonrec_Ty_tag c1 c2 tm)). Qed.
