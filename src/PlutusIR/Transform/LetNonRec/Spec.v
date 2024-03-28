From PlutusCert Require Import PlutusIR.
Import NamedTerm.
From PlutusCert Require Import PlutusIR.Transform.Compat.
From PlutusCert Require Import PlutusIR.Analysis.FreeVars.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Import Coq.Lists.List.ListNotations.


(* CNR = Compile Non-Recursive
   Desugaring strict, non-recursive lets into lambda-applications
*)
Inductive CNR_Term : Term -> Term -> Prop :=
  | CNR_Let : forall {bs t_body t_body' f_bs},
      CNR_Term t_body t_body' ->
      CNR_Bindings bs f_bs ->
      CNR_Term (Let NonRec bs t_body) (fold_right apply t_body' f_bs )
  | CNR_Compat : forall {t t'},
      Compat CNR_Term t t' ->
      CNR_Term t t'

(*
  `CNR_Bindings bs fs` states that each binding
   in the group `bs` can be desugared into t_bs
   where t_bs is of the form
     Apply (LamAbs (Apply (LamAbs ... t ...) t_1)) t_0
*)
with CNR_Bindings : list Binding -> list (Term -> Term) -> Prop :=
  | CNR_Nil  :
      CNR_Bindings nil nil
  | CNR_Cons : forall {b bs f_b f_bs},
      CNR_Binding        b   f_b ->
      CNR_Bindings       bs  f_bs ->
      CNR_Bindings (b :: bs) (f_b :: f_bs )

(* `CNR_Binding b f` states that the strict binding
      v = t_bound
    can be desugared into
      (\v -> t) t_bound
    for any term `t`
*)
with CNR_Binding : Binding -> (Term -> Term) -> Prop :=
  | CNR_Desugar : forall {v t_bound t_bound' ty},
      CNR_Term t_bound t_bound' ->
      CNR_Binding
        (TermBind Strict (VarDecl v ty) t_bound)
        (fun t_bs => Apply (LamAbs v ty t_bs) t_bound')
  .


