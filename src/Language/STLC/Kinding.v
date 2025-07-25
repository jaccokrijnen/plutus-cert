From PlutusCert Require Import STLC Util.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

From PlutusCert Require PlutusIR.


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


(* For Uni uses our own set kinding version for plutusIR*)
(** Kinding of types *)
Reserved Notation "Δ '|-*' T ':' K" (at level 40, T at level 0, K at level 0).
Inductive has_kind : list (PlutusIR.binderTyname * PlutusIR.kind) -> STLC.term -> PlutusIR.kind -> Set :=
  | K_Var : forall Δ X K,
      lookup X Δ = Some K ->
      Δ |-* (tmvar X) : K
  | K_Fun : forall Δ T1 T2,
      Δ |-* T1 : PlutusIR.Kind_Base ->
      Δ |-* T2 : PlutusIR.Kind_Base ->
      Δ |-* (@tmbin Fun T1 T2) : PlutusIR.Kind_Base
  | K_IFix  : forall Δ F T K,
      Δ |-* T : K ->
      Δ |-* F : (PlutusIR.Kind_Arrow (PlutusIR.Kind_Arrow K PlutusIR.Kind_Base) (PlutusIR.Kind_Arrow K PlutusIR.Kind_Base)) ->
      Δ |-* (@tmbin IFix F T) : PlutusIR.Kind_Base
  | K_Forall : forall Δ X K T,
      ((X, K) :: Δ) |-* T : PlutusIR.Kind_Base ->
      Δ |-* (@tmabs ForAll X K T) : PlutusIR.Kind_Base
  | K_Builtin : forall Δ T,
      Kinding.has_kind_uni T PlutusIR.Kind_Base ->
      Δ |-* (@tmbuiltin T) : PlutusIR.Kind_Base (* DefaultUni built in types must be fully applied with K_DefaultUniApply *)
  | K_Lam : forall Δ X K1 T K2,
      ((X, K1) :: Δ) |-* T : K2 ->
      Δ |-* (@tmabs Lam X K1 T) : (PlutusIR.Kind_Arrow K1 K2)
  | K_App : forall Δ T1 T2 K1 K2,
      Δ |-* T1 : (PlutusIR.Kind_Arrow K1 K2) ->
      Δ |-* T2 : K1 ->
      Δ |-* (@tmbin App T1 T2) : K2
where "Δ '|-*' T ':' K" := (has_kind Δ T K).