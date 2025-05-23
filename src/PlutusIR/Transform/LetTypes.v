From PlutusCert Require Import PlutusIR.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.


(* TODO: Combine this with LetNonRec
   currently desugares only a let-nonrec with only type bindings
*)

Inductive ty_let : term -> term -> Prop :=

  | tl_Let : forall bs t_body t_body' f_bs,
      ty_let t_body t_body' ->
      ty_let_Bindings bs f_bs ->
      ty_let (Let NonRec bs t_body) (fold_right apply t_body' f_bs )

  | tl_Compat : forall t t',
      Compat ty_let t t' ->
      ty_let t t'


with ty_let_Bindings : list binding -> list (term -> term) -> Prop :=

  | tl_Nil  :
      ty_let_Bindings nil nil

  | tl_Cons : forall {b bs f_b f_bs},
      ty_let_Binding        b   f_b ->
      ty_let_Bindings       bs  f_bs ->
      ty_let_Bindings (b :: bs) (f_b :: f_bs)

with ty_let_Binding : binding -> (term -> term) -> Prop :=
  | tl_Desugar : forall α k τ,
      ty_let_Binding
        (TypeBind (TyVarDecl α k) τ)
        (fun t_bs => TyInst (TyAbs α k t_bs) τ)
  .
