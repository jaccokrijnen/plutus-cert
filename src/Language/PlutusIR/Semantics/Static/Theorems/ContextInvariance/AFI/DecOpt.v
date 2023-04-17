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





(* appears_free_in_ty *)



QCDerive DecOpt for (appears_free_in_ty name ty).

Instance DecOptappears_free_in_ty_sound name ty: DecOptSoundPos (appears_free_in_ty name ty).
Proof. derive_sound. Qed. (* idtac "Admitted: DecOptappears_free_in_ty_sound". Admitted. *)

Instance DecOptappears_free_in_ty_complete name ty: DecOptCompletePos (appears_free_in_ty name ty).
Proof. derive_complete. Qed. (* idtac "Admitted: DecOptappears_free_in_ty_sound". Admitted. *)

Instance DecOptappears_free_in_ty_mon name ty: DecOptSizeMonotonic (appears_free_in_ty name ty).
Proof. derive_mon. Qed. (* idtac "Admitted: DecOptappears_free_in_ty_mon". Admitted. *)





(* appears_free_in_tm *)



MetaCoq Run (deriveCTProxy appears_free_in_tm).

Lemma appears_free_in_tm_proxy_sound : appears_free_in_tm_proxy_sound_type.
Proof. deriveCTProxy_sound core. Qed.

(* NOTE: I did not want to add the derivation for this proof type to CTProxy, since it
   is more complex than for the sound proof type, and for now it only seems to be necessary 
   for the proxy derived for the AFI relations.

   Another thing to note is that simply using auto also 'seems' to work, however, it simply
   applies the recursive functions without unfolding some underlying arguments. This is necessary
   since fixpoint need a decreasing argument, thus some of that unfolding has to be done manually
*)
Fixpoint appears_free_in_tm_tm_proxy_complete x x' (H: appears_free_in_tm x x') {struct H} : 
  appears_free_in_tm_proxy (appears_free_in_tm_tag x x')
with appears_free_in_tm_bindings_nonrec_proxy_complete x x' (H : appears_free_in_tm__bindings_nonrec x x') {struct H} :
  appears_free_in_tm_proxy (appears_free_in_tm__bindings_nonrec_tag x x')
with appears_free_in_tm_bindings_rec_proxy_complete x x' (H: appears_free_in_tm__bindings_rec x x') {struct H} :
  appears_free_in_tm_proxy (appears_free_in_tm__bindings_rec_tag x x')
with appears_free_in_tm_binding_proxy_complete x x' (H: appears_free_in_tm__binding x x') {struct H} :
  appears_free_in_tm_proxy (appears_free_in_tm__binding_tag x x').
Proof with auto.
  - inversion H; subst.
    1: constructor; auto.
    1: apply AFIT_LetNonRec_proxy; auto.
    1: apply AFIT_LetRec_proxy; auto.
    5: apply AFIT_Apply2_proxy; auto.
    all: constructor; auto.
  - inversion H; subst.
    + constructor; auto.
    + apply AFIT_ConsB2_NonRec_proxy; auto.
  - inversion H; subst.
    + constructor; auto.
    + apply AFIT_ConsB2_Rec_proxy; auto.
  - inversion H; subst. constructor. auto.
Qed.

Lemma appears_free_in_tm_proxy_complete : forall tag,
    match tag with
    | appears_free_in_tm__binding_tag x x0 => appears_free_in_tm__binding x x0
    | appears_free_in_tm__bindings_rec_tag x x0 => appears_free_in_tm__bindings_rec x x0
    | appears_free_in_tm__bindings_nonrec_tag x x0 => appears_free_in_tm__bindings_nonrec x x0
    | appears_free_in_tm_tag x x0 => appears_free_in_tm x x0
    end -> 
    appears_free_in_tm_proxy tag.
Proof with auto.
  intros tag H. destruct tag.
  - apply appears_free_in_tm_binding_proxy_complete...
  - apply appears_free_in_tm_bindings_rec_proxy_complete...
  - apply appears_free_in_tm_bindings_nonrec_proxy_complete...
  - apply appears_free_in_tm_tm_proxy_complete...
Qed.



QCDerive DecOpt for (appears_free_in_tm_proxy tag).

Instance DecOptappears_free_in_tm_proxy_sound tag : DecOptSoundPos (appears_free_in_tm_proxy tag).
Proof. derive_sound. Qed. (* idtac "Admitted: DecOptappears_free_in_tm_proxy_sound". Admitted. *)

Instance DecOptappears_free_in_tm_proxy_complete tag : DecOptCompletePos (appears_free_in_tm_proxy tag).
Proof. derive_complete. Qed. (* idtac "Admitted: DecOptappears_free_in_tm_proxy_complete". Admitted. *)

Instance DecOptappears_free_in_tm_proxy_mon tag: DecOptSizeMonotonic (appears_free_in_tm_proxy tag).
Proof. derive_mon. Qed. (* idtac "Admitted: DecOptappears_free_in_tm_proxy_mon". Admitted. *)


(* appears_free_in_tm *)

Instance DecOptappears_free_in_tm name tm : DecOpt (appears_free_in_tm name tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm_tag name tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm_tag name tm)) s |}.

Instance DecOptappears_free_in_tm_sound name tm : DecOptSoundPos (appears_free_in_tm name tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm_tag name tm)). Qed.

Instance DecOptappears_free_in_tm_complete name tm : DecOptCompletePos (appears_free_in_tm name tm).
Proof. derive__complete (appears_free_in_tm_proxy_complete). Qed.

Instance DecOptappears_free_in_tm_mon name tm: DecOptSizeMonotonic (appears_free_in_tm name tm).
Proof. apply DecOptappears_free_in_tm_proxy_mon. Qed.



(* appears_free_in_tm__bindings_nonrec *)

Instance DecOptappears_free_in_tm__bindings_nonrec bs tm : DecOpt (appears_free_in_tm__bindings_nonrec bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__bindings_nonrec_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__bindings_nonrec_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__bindings_nonrec_sound bs tm : DecOptSoundPos (appears_free_in_tm__bindings_nonrec bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__bindings_nonrec_tag bs tm)). Qed.

Instance DecOptappears_free_in_tm__bindings_nonrec_complete bs tm : DecOptCompletePos (appears_free_in_tm__bindings_nonrec bs tm).
Proof. derive__complete (appears_free_in_tm_proxy_complete). Qed.

Instance DecOptappears_free_in_tm__bindings_nonrec_mon name tm: DecOptSizeMonotonic (appears_free_in_tm__bindings_nonrec name tm).
Proof. apply DecOptappears_free_in_tm_proxy_mon. Qed.



(* appears_free_in_tm__bindings_rec *)

Instance DecOptappears_free_in_tm__bindings_rec bs tm : DecOpt (appears_free_in_tm__bindings_rec bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__bindings_rec_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__bindings_rec_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__bindings_rec_sound bs tm : DecOptSoundPos (appears_free_in_tm__bindings_rec bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__bindings_rec_tag bs tm)). Qed.

Instance DecOptappears_free_in_tm__bindings_rec_complete bs tm : DecOptCompletePos (appears_free_in_tm__bindings_rec bs tm).
Proof. derive__complete (appears_free_in_tm_proxy_complete). Qed.

Instance DecOptappears_free_in_tm__bindings_rec_mon name tm: DecOptSizeMonotonic (appears_free_in_tm__bindings_rec name tm).
Proof. apply DecOptappears_free_in_tm_proxy_mon. Qed.



(* appears_free_in_tm__binding *)

Instance DecOptappears_free_in_tm__binding bs tm : DecOpt (appears_free_in_tm__binding bs tm) :=
{| decOpt s := @decOpt (appears_free_in_tm_proxy (appears_free_in_tm__binding_tag bs tm)) (DecOptappears_free_in_tm_proxy (appears_free_in_tm__binding_tag bs tm)) s |}.

Instance DecOptappears_free_in_tm__binding_sound bs tm : DecOptSoundPos (appears_free_in_tm__binding bs tm).
Proof. derive__sound (appears_free_in_tm_proxy_sound (appears_free_in_tm__binding_tag bs tm)). Qed.

Instance DecOptappears_free_in_tm__binding_complete bs tm : DecOptCompletePos (appears_free_in_tm__binding bs tm).
Proof. derive__complete (appears_free_in_tm_proxy_complete). Qed.

Instance DecOptappears_free_in_tm__binding_mon name tm: DecOptSizeMonotonic (appears_free_in_tm__binding name tm).
Proof. apply DecOptappears_free_in_tm_proxy_mon. Qed.





(* appears_free_in_ann *)



MetaCoq Run (deriveCTProxy appears_free_in_ann).

Lemma appears_free_in_ann_proxy_sound : appears_free_in_ann_proxy_sound_type.
Proof. deriveCTProxy_sound core. Qed.



QCDerive DecOpt for (appears_free_in_ann_proxy tag).

Instance DecOptappears_free_in_ann_proxy_sound tag : DecOptSoundPos (appears_free_in_ann_proxy tag).
Proof. derive_sound. Qed. (* idtac "Admitted: DecOptappears_free_in_ann_proxy_sound". Admitted. *)

Instance DecOptappears_free_in_ann_proxy_complete tag : DecOptCompletePos (appears_free_in_ann_proxy tag).
Proof. derive_complete. Qed. (* idtac "Admitted: DecOptappears_free_in_ann_proxy_complete". Admitted. *)

Instance DecOptappears_free_in_ann_proxy_mon tag : DecOptSizeMonotonic (appears_free_in_ann_proxy tag).
Proof. derive_mon. Qed. (* idtac "Admitted: DecOptappears_free_in_ann_proxy_mon". Admitted. *)


Fixpoint appears_free_in_ann_ann_proxy_complete x x' (H: appears_free_in_ann x x') {struct H} : 
  appears_free_in_ann_proxy (appears_free_in_ann_tag x x')
with appears_free_in_ann_constructor_proxy_complete x x' (H : appears_free_in_ann__constructor x x') {struct H} :
  appears_free_in_ann_proxy (appears_free_in_ann__constructor_tag x x')
with appears_free_in_ann_bindings_nonrec_proxy_complete x x' (H : appears_free_in_ann__bindings_nonrec x x') {struct H} :
  appears_free_in_ann_proxy (appears_free_in_ann__bindings_nonrec_tag x x')
with appears_free_in_ann_bindings_rec_proxy_complete x x' (H: appears_free_in_ann__bindings_rec x x') {struct H} :
  appears_free_in_ann_proxy (appears_free_in_ann__bindings_rec_tag x x')
with appears_free_in_ann_binding_proxy_complete x x' (H: appears_free_in_ann__binding x x') {struct H} :
  appears_free_in_ann_proxy (appears_free_in_ann__binding_tag x x').
Proof with auto.
  - inversion H; subst.
    1: constructor; auto.
    1: apply AFIA_LetNonRec_proxy; auto.
    1: apply AFIA_LetRec_proxy; auto.
    3: apply AFIA_LamAbs2_proxy; auto.
    4: apply AFIA_Apply2_proxy; auto.
    5: apply AFIA_TyInst2_proxy; auto.
    6: apply AFIA_IWrap2_proxy; auto.
    6: apply AFIA_IWrap3_proxy; auto.
    all: constructor; auto.
  - inversion H; subst.
    + constructor; auto.
    + apply AFIA_Constructor_There_proxy; auto.
  - inversion H; subst.
    + constructor; auto.
    + apply AFIA_ConsB2_NonRec_proxy; auto.
  - inversion H; subst.
    + constructor; auto.
    + apply AFIA_ConsB2_Rec_proxy; auto.
  - inversion H; subst. 
    + constructor. auto.
    + apply AFIA_TermBind2_proxy; auto.
    + apply AFIA_TypeBind_proxy; auto.
    + apply AFIA_DatatypeBind1_proxy; auto.
Qed.

Lemma appears_free_in_ann_proxy_complete : forall tag,
    match tag with
    | appears_free_in_ann__binding_tag x x0 => appears_free_in_ann__binding x x0
    | appears_free_in_ann__constructor_tag x x0 => appears_free_in_ann__constructor x x0
    | appears_free_in_ann__bindings_rec_tag x x0 => appears_free_in_ann__bindings_rec x x0
    | appears_free_in_ann__bindings_nonrec_tag x x0 => appears_free_in_ann__bindings_nonrec x x0
    | appears_free_in_ann_tag x x0 => appears_free_in_ann x x0
    end -> 
    appears_free_in_ann_proxy tag.
Proof with auto.
  intros tag H. destruct tag.
  - apply appears_free_in_ann_binding_proxy_complete...
  - apply appears_free_in_ann_bindings_rec_proxy_complete...
  - apply appears_free_in_ann_bindings_nonrec_proxy_complete...
  - apply appears_free_in_ann_constructor_proxy_complete...
  - apply appears_free_in_ann_ann_proxy_complete...
Qed.



(* appears_free_in_ann *)

Instance DecOptappears_free_in_ann name ann : DecOpt (appears_free_in_ann name ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann_tag name ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann_tag name ann)) s |}.

Instance DecOptappears_free_in_ann_sound name ann : DecOptSoundPos (appears_free_in_ann name ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann_tag name ann)). Qed.

Instance DecOptappears_free_in_ann_complete name tm : DecOptCompletePos (appears_free_in_ann name tm).
Proof. derive__complete (appears_free_in_ann_proxy_complete). Qed.

Instance DecOptappears_free_in_ann_mon name tm: DecOptSizeMonotonic (appears_free_in_ann name tm).
Proof. apply DecOptappears_free_in_ann_proxy_mon. Qed.



(* appears_free_in_ann__constructor *)

Instance DecOptappears_free_in_ann__constructor bs ann : DecOpt (appears_free_in_ann__constructor bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__constructor_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__constructor_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__constructor_sound bs ann : DecOptSoundPos (appears_free_in_ann__constructor bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__constructor_tag bs ann)). Qed.

Instance DecOptappears_free_in_ann__constructor_complete name tm : DecOptCompletePos (appears_free_in_ann__constructor name tm).
Proof. derive__complete (appears_free_in_ann_proxy_complete). Qed.

Instance DecOptappears_free_in_ann__constructor_mon name tm: DecOptSizeMonotonic (appears_free_in_ann__constructor name tm).
Proof. apply DecOptappears_free_in_ann_proxy_mon. Qed.



(* appears_free_in_ann__bindings_nonrec *)

Instance DecOptappears_free_in_ann__bindings_nonrec bs ann : DecOpt (appears_free_in_ann__bindings_nonrec bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__bindings_nonrec_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__bindings_nonrec_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__bindings_nonrec_sound bs ann : DecOptSoundPos (appears_free_in_ann__bindings_nonrec bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__bindings_nonrec_tag bs ann)). Qed.

Instance DecOptappears_free_in_ann__bindings_nonrec_complete name tm : DecOptCompletePos (appears_free_in_ann__bindings_nonrec name tm).
Proof. derive__complete (appears_free_in_ann_proxy_complete). Qed.

Instance DecOptappears_free_in_ann__bindings_nonrec_mon name tm: DecOptSizeMonotonic (appears_free_in_ann__bindings_nonrec name tm).
Proof. apply DecOptappears_free_in_ann_proxy_mon. Qed.



(* appears_free_in_ann__bindings_rec *)

Instance DecOptappears_free_in_ann__bindings_rec bs ann : DecOpt (appears_free_in_ann__bindings_rec bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__bindings_rec_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__bindings_rec_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__bindings_rec_sound bs ann : DecOptSoundPos (appears_free_in_ann__bindings_rec bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__bindings_rec_tag bs ann)). Qed.

Instance DecOptappears_free_in_ann__bindings_rec_complete name tm : DecOptCompletePos (appears_free_in_ann__bindings_rec name tm).
Proof. derive__complete (appears_free_in_ann_proxy_complete). Qed.

Instance DecOptappears_free_in_ann__bindings_rec_mon name tm: DecOptSizeMonotonic (appears_free_in_ann__bindings_rec name tm).
Proof. apply DecOptappears_free_in_ann_proxy_mon. Qed.




(* appears_free_in_ann__binding *)

Instance DecOptappears_free_in_ann__binding bs ann : DecOpt (appears_free_in_ann__binding bs ann) :=
{| decOpt s := @decOpt (appears_free_in_ann_proxy (appears_free_in_ann__binding_tag bs ann)) (DecOptappears_free_in_ann_proxy (appears_free_in_ann__binding_tag bs ann)) s |}.

Instance DecOptappears_free_in_ann__binding_sound bs ann : DecOptSoundPos (appears_free_in_ann__binding bs ann).
Proof. derive__sound (appears_free_in_ann_proxy_sound (appears_free_in_ann__binding_tag bs ann)). Qed.

Instance DecOptappears_free_in_ann__binding_complete name tm : DecOptCompletePos (appears_free_in_ann__binding name tm).
Proof. derive__complete (appears_free_in_ann_proxy_complete). Qed.

Instance DecOptappears_free_in_ann__binding_mon name tm: DecOptSizeMonotonic (appears_free_in_ann__binding name tm).
Proof. apply DecOptappears_free_in_ann_proxy_mon. Qed.
