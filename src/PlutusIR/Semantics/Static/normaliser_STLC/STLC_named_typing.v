From PlutusCert Require Import STLC_named Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

From PlutusCert Require Import PlutusIR.


Reserved Notation "'|-*_uni' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind_uni : DefaultUni -> kind -> Set :=
  | K_DefaultUniInteger :
      |-*_uni DefaultUniInteger : Kind_Base
  | K_DefaultUniByteString :
      |-*_uni DefaultUniByteString : Kind_Base
  | K_DefaultUniString :
      |-*_uni DefaultUniString : Kind_Base
  | K_DefaultUniUnit :
      |-*_uni DefaultUniUnit : Kind_Base
  | K_DefaultUniBool :
      |-*_uni DefaultUniBool : Kind_Base
  | K_DefaultUniData :
      |-*_uni DefaultUniData : Kind_Base
  | K_DefaultUniBLS12_381_G1_Element :
      |-*_uni DefaultUniBLS12_381_G1_Element : Kind_Base
  | K_DefaultUniBLS12_381_G2_Element :
      |-*_uni DefaultUniBLS12_381_G2_Element : Kind_Base
  | K_DefaultUniBLS12_381_MlResult :
      |-*_uni DefaultUniBLS12_381_MlResult : Kind_Base
  | K_DefaultUniApply k k' t t':
      |-*_uni t : (Kind_Arrow k k') ->
      |-*_uni t' : k ->
      |-*_uni (DefaultUniApply t t') : k'
  | K_DefaultUniProtoPair :
      |-*_uni DefaultUniProtoPair : (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base Kind_Base))
  | K_DefaultUniProtoList :
      |-*_uni DefaultUniProtoList : (Kind_Arrow Kind_Base Kind_Base)
  where "'|-*_uni' T ':' K" := (has_kind_uni T K)
.


(* Example ill-kinded:
nil |-* TyApp (Lam bX Kind_Base "bX") (Lam bY Kind_Base "bY")

So then: nil |-* (Lam bY Kind_Base "bY") : K1a -> K1b
(bY, Kind_Base) |-* "bY" : Kind_Base = K1b
also K1a = K1b = Kind_Base
Hence K1 := Kind_Base -> Kind_Base

lam bX Kind_Base "bX" : (KB -> KB) -> K2 ?
No, because it is KB -> KB in total.
No way to unify (KB -> KB) -> K2 with KB -> KB

*)

(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : list (binderTyname * kind) -> STLC_named.term -> kind -> Set :=
  | K_Var : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-* (tmvar X) : K
  | K_Fun : forall Δ T1 T2,
      Δ |-* T1 : Kind_Base ->
      Δ |-* T2 : Kind_Base ->
      Δ |-* (@tmapp Fun T1 T2) : Kind_Base
  | K_IFix  : forall Δ F T K,
      Δ |-* T : K ->
      Δ |-* F : (Kind_Arrow (Kind_Arrow K Kind_Base) (Kind_Arrow K Kind_Base)) ->
      Δ |-* (@tmapp IFix F T) : Kind_Base
  | K_Forall : forall Δ X K T,
      ((X, K) :: Δ) |-* T : Kind_Base ->
      Δ |-* (@tmlam ForAll X K T) : Kind_Base
  | K_Builtin : forall Δ T,
      |-*_uni T : Kind_Base ->
      Δ |-* (@tmbuiltin T) : Kind_Base (* DefaultUni built in types must be fully applied with K_DefaultUniApply *)
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (@tmlam Lam X K1 T) : (Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (@tmapp App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).