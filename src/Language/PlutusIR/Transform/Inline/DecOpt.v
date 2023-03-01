From PlutusCert Require Import
  Util.List
  Util.DecOpt
  Language.PlutusIR
  Language.PlutusIR.DecOpt
  Language.PlutusIR.Transform.Inline
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







MetaCoq Run (deriveCTProxy inline).

Local Hint Constructors 
  inline 
  inline_Bindings_Rec 
  inline_Bindings_NonRec 
  inline_Binding 
  inline_Ty 
  inline_Var
    : inline_hints. 

Lemma inline_proxy_sound : inline_proxy_sound_type.
Proof. deriveCTProxy_sound inline_hints. Qed.





QCDerive DecOpt for (inline_proxy tag).

Instance DecOptinline_proxy_sound tag : DecOptSoundPos (inline_proxy tag).
Proof. (* derive_sound. Qed. *) idtac "Admitted: DecOptinline_proxy_sound". Admitted.



(* inline *)

Instance DecOptinline c1 c2 tm : DecOpt (inline c1 c2 tm) :=
{| decOpt s := @decOpt (inline_proxy (inline_tag c1 c2 tm)) (DecOptinline_proxy (inline_tag c1 c2 tm)) s |}.

Instance DecOptinline_sound c1 c2 tm : DecOptSoundPos (inline c1 c2 tm).
Proof. derive__sound (inline_proxy_sound (inline_tag c1 c2 tm)). Qed.



(* inline_Bindings_Rec *)

Instance DecOptinline_Bindings_Rec c1 c2 tm : DecOpt (inline_Bindings_Rec c1 c2 tm) :=
{| decOpt s := @decOpt (inline_proxy (inline_Bindings_Rec_tag c1 c2 tm)) (DecOptinline_proxy (inline_Bindings_Rec_tag c1 c2 tm)) s |}.

Instance DecOptinline_Bindings_Rec_sound c1 c2 tm : DecOptSoundPos (inline_Bindings_Rec c1 c2 tm).
Proof. derive__sound (inline_proxy_sound (inline_Bindings_Rec_tag c1 c2 tm)). Qed.



(* inline_Bindings_NonRec *)

Instance DecOptinline_Bindings_NonRec c1 c2 tm : DecOpt (inline_Bindings_NonRec c1 c2 tm) :=
{| decOpt s := @decOpt (inline_proxy (inline_Bindings_NonRec_tag c1 c2 tm)) (DecOptinline_proxy (inline_Bindings_NonRec_tag c1 c2 tm)) s |}.

Instance DecOptinline_Bindings_NonRec_sound c1 c2 tm : DecOptSoundPos (inline_Bindings_NonRec c1 c2 tm).
Proof. derive__sound (inline_proxy_sound (inline_Bindings_NonRec_tag c1 c2 tm)). Qed.



(* inline_Binding *)

Instance DecOptinline_Binding c1 c2 tm : DecOpt (inline_Binding c1 c2 tm) :=
{| decOpt s := @decOpt (inline_proxy (inline_Binding_tag c1 c2 tm)) (DecOptinline_proxy (inline_Binding_tag c1 c2 tm)) s |}.

Instance DecOptinline_Binding_sound c1 c2 tm : DecOptSoundPos (inline_Binding c1 c2 tm).
Proof. derive__sound (inline_proxy_sound (inline_Binding_tag c1 c2 tm)). Qed.



(* inline_Ty *)

Instance DecOptinline_Ty c1 c2 tm : DecOpt (inline_Ty c1 c2 tm) :=
{| decOpt s := @decOpt (inline_proxy (inline_Ty_tag c1 c2 tm)) (DecOptinline_proxy (inline_Ty_tag c1 c2 tm)) s |}.

Instance DecOptinline_Ty_sound c1 c2 tm : DecOptSoundPos (inline_Ty c1 c2 tm).
Proof. derive__sound (inline_proxy_sound (inline_Ty_tag c1 c2 tm)). Qed.
