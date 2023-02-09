From PlutusCert Require Import
  Util
  Util.List
  Language.PlutusIR
  Analysis.BoundVars.
Import NamedTerm.

Require Import
  Strings.String
  Lists.List
.

Import ListNotations.
From QuickChick Require Import QuickChick.
From Sandbox Require Import CTProxy.
Require Import Coq.Program.Equality.





Definition ctx := list string.

Definition tvd_name (tvd : tvdecl tyname) : tyname :=
  match tvd with
  | TyVarDecl v K => v
  end.

Reserved Notation "Δ '|-*' T" (at level 40, T at level 0).
Inductive well_scoped_Ty (Δ : ctx) : Ty -> Prop :=
  | WST_Var : forall X,
      NameIn X Δ ->
      Δ |-* (Ty_Var X)
  | WST_Fun : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_Fun T1 T2)
  | WST_IFix  : forall F T,
      Δ |-* T ->
      Δ |-* F ->
      Δ |-* (Ty_IFix F T)
  | WST_Forall : forall X K T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Forall X K T)
  | WST_Builtin : forall u (x : typeIn u),
      Δ |-* (Ty_Builtin (Some' x))
  | WST_Lam : forall X K1 T,
      (X :: Δ) |-* T ->
      Δ |-* (Ty_Lam X K1 T)
  | WST_App : forall T1 T2,
      Δ |-* T1 ->
      Δ |-* T2 ->
      Δ |-* (Ty_App T1 T2) 
where "Δ '|-*' T " := (well_scoped_Ty Δ T).

QCDerive DecOpt for (well_scoped_Ty Δ ty).

Instance DecOptwell_scoped_Ty_sound Δ ty: DecOptSoundPos (well_scoped_Ty Δ ty).
Proof. derive_sound. Qed.






Reserved Notation "Δ ',,' Γ '|-+' t " (at level 101, t at level 0, no associativity).
Reserved Notation "Δ '|-ok_cs' c " (at level 101, c at level 0).
Reserved Notation "Δ ',,' Γ  '|-oks_nr' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-oks_r' bs" (at level 101, bs at level 0, no associativity).
Reserved Notation "Δ ',,' Γ '|-ok_b' b" (at level 101, b at level 0, no associativity).

Inductive constructors_well_formed (Δ : ctx) : list constructor -> Prop :=
  | W_Con : forall x T ar cs,
      Δ |-* T ->
      Δ |-ok_cs cs ->
      Δ |-ok_cs ((Constructor (VarDecl x T) ar) :: cs)
  where 
    "Δ '|-ok_cs' cs" := (constructors_well_formed Δ cs).

QCDerive DecOpt for (constructors_well_formed Δ c).

Instance DecOptconstructors_well_formed_sound Δ c : DecOptSoundPos (constructors_well_formed Δ c).
Proof. derive_sound. Qed.





Definition btvb_app (b : Binding) Δ := btvb b ++ Δ.
Definition bvb_app (b : Binding) Δ := bvb b ++ Δ.
Definition map_tvd_name_rev_app x c := rev (map tvd_name x) ++ c.
Definition rev_btvbs_app (x : list Binding) c := rev (btvbs x) ++ c.
Definition rev_bvbs_app (x : list Binding) c := rev (bvbs x) ++ c.

Inductive well_scoped (Δ Γ: ctx) : Term -> Prop :=
  | WS_Var : forall x,
      NameIn x Γ ->
      Δ ,, Γ |-+ (Var x)
  | WS_LamAbs : forall x T t,
      Δ |-* T ->
      Δ ,, (x :: Γ) |-+ t ->
      Δ ,, Γ |-+ (LamAbs x T t)
  | WS_Apply : forall t1 t2,
      Δ ,, Γ |-+ t1 ->
      Δ ,, Γ |-+ t2 ->
      Δ ,, Γ |-+ (Apply t1 t2)
  (* Universal types *)
  | WS_TyAbs : forall X K t,
      (X :: Δ) ,, Γ |-+ t ->
      Δ ,, Γ |-+ (TyAbs X K t)
  | WS_TyInst : forall t T,
      Δ ,, Γ |-+ t ->
      Δ |-* T ->
      Δ ,, Γ |-+ (TyInst t T)
  | WS_IWrap : forall F T M,
      Δ |-* F ->
      Δ |-* T ->
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (IWrap F T M)
  | WS_Unwrap : forall M,
      Δ ,, Γ |-+ M ->
      Δ ,, Γ |-+ (Unwrap M)
  | WS_Constant : forall u (x : valueOf u),
      Δ ,, Γ |-+ (Constant (Some' x))
  | WS_Builtin : forall f,
      Δ ,, Γ |-+ (Builtin f)
  | WS_Error : forall s,
      Δ |-* s ->
      Δ ,, Γ |-+ (Error s)
  | WS_Let : forall bs t Δ' Γ',
      Δ' = rev_btvbs_app bs Δ ->
      Γ' = rev_bvbs_app bs Γ ->
      Δ ,, Γ |-oks_nr bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let NonRec bs t)
  | WS_LetRec : forall bs t Δ' Γ',
      Δ' = rev_btvbs_app bs Δ ->
      Γ' = rev_bvbs_app bs Γ ->
      Δ' ,, Γ' |-oks_r bs ->
      Δ' ,, Γ' |-+ t ->
      Δ ,, Γ |-+ (Let Rec bs t)
          
with bindings_well_formed_nonrec (Δ Γ : ctx) : list Binding -> Prop :=
  | W_NilB_NonRec :
      Δ ,, Γ |-oks_nr nil
  | W_ConsB_NonRec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      (btvb_app b Δ) ,, (bvb_app b Γ) |-oks_nr bs ->
      Δ ,, Γ |-oks_nr (b :: bs)

with bindings_well_formed_rec (Δ Γ : ctx) : list Binding -> Prop :=
  | W_NilB_Rec :
      Δ ,, Γ |-oks_r nil
  | W_ConsB_Rec : forall b bs,
      Δ ,, Γ |-ok_b b ->
      Δ ,, Γ |-oks_r bs ->
      Δ ,, Γ |-oks_r (b :: bs)

with binding_well_formed (Δ Γ : ctx) : Binding -> Prop :=
  | W_Term : forall s x T t,
      Δ |-* T ->
      Δ ,, Γ |-+ t ->
      Δ ,, Γ |-ok_b (TermBind s (VarDecl x T) t)
  | W_Type : forall X K T,
      Δ |-* T ->
      Δ ,, Γ |-ok_b (TypeBind (TyVarDecl X K) T)
  | W_Data : forall X YKs cs matchFunc Δ',
      Δ' = map_tvd_name_rev_app YKs Δ  ->
      Δ' |-ok_cs cs ->
      Δ ,, Γ |-ok_b (DatatypeBind (Datatype X YKs matchFunc cs))

  where "Δ ',,' Γ '|-+' t" := (well_scoped Δ Γ t)
  and "Δ ',,' Γ '|-oks_nr' bs" := (bindings_well_formed_nonrec Δ Γ bs)
  and "Δ ',,' Γ '|-oks_r' bs" := (bindings_well_formed_rec Δ Γ bs)
  and "Δ ',,' Γ '|-ok_b' b" := (binding_well_formed Δ Γ b).

(* derivation of proxy type *)
MetaCoq Run (deriveCTProxy well_scoped).




(* derivation over proxy type*)
QCDerive DecOpt for (well_scoped_proxy tag).

Instance DecOptwell_scoped_proxy_sound tag : DecOptSoundPos (well_scoped_proxy tag).
Proof. (* derive_sound. Qed. *) Admitted.



Theorem well_scoped_proxy_sound : well_scoped_proxy_sound_type.
Proof.
  intros tag H; induction H; subst; eauto using well_scoped, bindings_well_formed_nonrec, bindings_well_formed_rec, binding_well_formed. 
Qed.





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



Definition closed := well_scoped [] [].
