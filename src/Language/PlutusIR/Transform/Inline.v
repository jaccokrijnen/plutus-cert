Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PeanoNat.

Import ListNotations.
From Equations Require Import Equations.
Require Import Program.
Require Import Lia.

Set Implicit Arguments.
Set Equations Transparent.

From PlutusCert Require Import Util.
From PlutusCert Require Import Language.PlutusIR.
From PlutusCert Require Import Language.PlutusIR.Analysis.FreeVars.
From PlutusCert Require Import Language.PlutusIR.Transform.Congruence.
(* EDIT_JORIS :  From PlutusCert Require Import Language.PlutusIR.Examples. *)
From PlutusCert Require Import Language.PlutusIR.Optimizer.DeadBindings.





Generalizable All Variables.
Definition Env := list (prod string Term).

(* list of term bindings *)
Fixpoint bindingsToEnv (bs : list Binding) : Env :=
  match bs with
    | nil                              =>  nil
    | TermBind _ v t :: bs => (v, t) :: bindingsToEnv bs
    | _                          :: bs =>           bindingsToEnv bs
  end.

(*
This relation relates terms where inlining of let-bound variables may
have taken place. Note that the PIR inliner may also remove the let binding
when all of its occurrences have been inlined. This is not taken into account here.

When relating the subsequent ASTs dumped by the compiler we tehrefore have to search
for a composition of `Inline` and `DBE_Term`.
*)
Inductive Inline : Env -> Term -> Term -> Type :=

  (* Extend env and recurse in bound terms, possibly remove
     dead bindings *)
  | Inl_Let    : `{    env' = bindingsToEnv bs ++ env        (* extend env with bindings in group *)
                    (* Todo: take care of non-recursive binding groups, those binders
                             refer to eachother *)

                    -> Inline_Bindings env' bs bs'           (* Bound terms may have inlined variables*)
                    -> Inline env' t t'
                    -> Inline env (Let r bs  t )
                                  (Let r bs' t') }

  (* Term did not change, note that a search should be biased for Inl_Let as
     it will extend the environment (exclude Let from Cong somehow?) *)
  | Inl_Cong   : `{ Cong (Inline env) t t' -> Inline env t t'}

  | Inl_Var    : `{ In (v, t) env -> Inline env t t' -> Inline env (Var v) t'}


  (* Recognize inlinings in a group of bindings *)
  (* TODO: this is map-ish boilerplate*)
  with Inline_Bindings : Env -> list Binding -> list Binding -> Type :=
  | Inl_Binding_cons : `{  Inline_Binding env b b'
                        -> Inline_Bindings env bs bs'
                        -> Inline_Bindings env (b :: bs) (b' :: bs')  }
  | Inl_Binding_nil  : `{ Inline_Bindings env nil nil}


  (* Recognize inlining in a single binding*)
  (* TODO: this is boilerplate, in that we're only traversing
     Terms within the binding *)
  with Inline_Binding : Env -> Binding -> Binding -> Type :=
  | Inl_TermBind  : `{ Inline env t t' (* This does not allow inlinings of a recursive definition, perhaps allow?*)
                     -> Inline_Binding env (TermBind r v t)
                                           (TermBind r v t')}
  | Inl_OtherBind : `{ Inline_Binding env b b}.

(* PIR inlining step is composition of inline with dbe *)
Inductive PIR_Inline t t'' :=
  Comp_Inl_DBE: forall t', Inline nil t t' -> DBE_Term t' t'' -> PIR_Inline t t''.

