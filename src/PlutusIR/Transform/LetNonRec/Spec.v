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
  | CNR_LetNonRec : forall {bs t_body t_body' f_bs},
      CNR_Term t_body t_body' ->
      CNR_Bindings bs f_bs ->
      CNR_Term (Let NonRec bs t_body) (fold_right apply t_body' f_bs )

  (* Compatibility cases *)
  | CNR_LetRec : forall bs bs' t_body t_body',
      CNR_Term t_body t_body' ->
      CNR_LetRec_compat bs bs' ->
      CNR_Term (Let Rec bs t_body) (Let Rec bs' t_body')
  | CNR_Var : compat_Var CNR_Term
  | CNR_TyAbs : compat_TyAbs CNR_Term
  | CNR_LamAbs : compat_LamAbs CNR_Term
  | CNR_Apply : compat_Apply CNR_Term
  | CNR_Constant : compat_Constant CNR_Term
  | CNR_Builtin : compat_Builtin CNR_Term
  | CNR_TyInst : compat_TyInst CNR_Term
  | CNR_Error : compat_Error CNR_Term
  | CNR_IWrap : compat_IWrap CNR_Term
  | CNR_Unwrap : compat_Unwrap CNR_Term
  | CNR_Constr : compat_Constr CNR_Term
  | CNR_Case : compat_Case CNR_Term

  (*
  | CNR_Compat : forall {t t'},
      Compat CNR_Term t t' ->
      CNR_Term t t'
      *)

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
with CNR_LetRec_compat : list Binding -> list Binding -> Prop :=
  | CNR_LetRec_nil :
      CNR_LetRec_compat [] []
  | CNR_LetRec_cons : forall b b' bs bs',
      CNR_Binding_compat b b' ->
      CNR_LetRec_compat bs bs' ->
      CNR_LetRec_compat (b::bs) (b'::bs')
with CNR_Binding_compat : Binding -> Binding -> Prop :=
  | CNR_TermBind : compat_TermBind CNR_Term CNR_Binding_compat
  | CNR_DatatypeBind : compat_DatatypeBind CNR_Binding_compat
  | CNR_TypeBind : compat_TypeBind CNR_Binding_compat
  .


Scheme CNR__ind := Minimality for CNR_Term Sort Prop
  with CNR_Bindings__ind := Minimality for CNR_Bindings Sort Prop
  with CNR_Binding__ind := Minimality for CNR_Binding Sort Prop
  with CNR_LetRec_compat__ind := Minimality for CNR_LetRec_compat Sort Prop
  with CNR_Binding_compat__ind := Minimality for CNR_Binding_compat Sort Prop
.

Combined Scheme CNR__multind from
  CNR__ind,
  CNR_Bindings__ind,
  CNR_Binding__ind,
  CNR_LetRec_compat__ind,
  CNR_Binding_compat__ind
.
