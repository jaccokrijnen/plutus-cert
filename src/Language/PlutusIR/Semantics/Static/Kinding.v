Require Import PlutusCert.Language.PlutusIR.
Import NamedTerm.

Require Export PlutusCert.Language.PlutusIR.Semantics.Static.Context.

(** Kinds of built-in types *)
Definition lookupBuiltinKind (u : DefaultUni) : Kind := 
  match u with
  | DefaultUniInteger    => Kind_Base
  | DefaultUniByteString => Kind_Base
  | DefaultUniString     => Kind_Base
  | DefaultUniChar       => Kind_Base
  | DefaultUniUnit       => Kind_Base
  | DefaultUniBool       => Kind_Base
  end.

(** Kinding of types *)
Reserved Notation "Delta '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : Delta -> Ty -> Kind -> Prop :=
  | K_Var : forall Delta X K,
      Delta X = Coq.Init.Datatypes.Some K ->
      Delta |-* (Ty_Var X) : K
  | K_Fun : forall Delta T1 T2,
      Delta |-* T1 : Kind_Base ->
      Delta |-* T2 : Kind_Base ->
      Delta |-* (Ty_Fun T1 T2) : Kind_Base
  | K_IFix  : forall Delta F T K,
      Delta |-* T : K ->
      Delta |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Delta |-* (Ty_IFix F T) : Kind_Base
  | K_Forall : forall Delta X K T,
      (X |-> K; Delta) |-* T : Kind_Base ->
      Delta |-* (Ty_Forall X K T) : Kind_Base
  | K_Builtin : forall Delta u T,
      T = lookupBuiltinKind u ->
      Delta |-* (Ty_Builtin (Some (TypeIn u))) : T
  | K_Lam : forall Delta X K1 T K2,
      (X |-> K1; Delta) |-* T : K2 ->
      Delta |-* (Ty_Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Delta T1 T2 K1 K2,
      Delta |-* T1 : (Kind_Arrow K1 K2) ->
      Delta |-* T2 : K1 ->
      Delta |-* (Ty_App T1 T2) : K2
where "Delta '|-*' T ':' K" := (has_kind Delta T K).