From PlutusCert Require Import
  Util.List
  Util.DecOpt
  Language.PlutusIR
  Language.PlutusIR.DecOpt
  Language.PlutusIR.Transform.Inline
  Language.PlutusIR.Analysis.Equality.DecOpt.

From QuickChick Require Import QuickChick.
From CTProxy Require Import CTProxy.


Instance EnumSizedbinder_info : EnumSized binder_info :=
  {| enumSized _ := ret (bound_ty (Ty_Var EmptyString)) |}.

Instance Dec_eq_binder_info : Dec_Eq binder_info.
Proof.
  constructor.
  unfold ssrbool.decidable.
  decide equality.
  - apply Dec_eq_Term.
  - apply Dec_eq_Ty.
Defined.

Instance Dec_eq_ctx : Dec_Eq ctx.
Proof.
  apply Dec_eq_list.
  apply Dec_eq_prod.
  - apply Dec_eq_string.
  - apply Dec_eq_binder_info.
Defined.


QCDerive DecOpt for (inline_ty c1 c2 ty1 ty2).

Instance DecOptinline_ty_sound c1 c2 ty1 ty2 : DecOptSoundPos (inline_ty c1 c2 ty1 ty2).
Proof. derive_sound. Qed.


MetaCoq Run (deriveCTProxy inline).

Local Hint Constructors 
  inline 
  inline_Bindings_Rec 
  inline_Bindings_NonRec 
  inline_Binding 
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
