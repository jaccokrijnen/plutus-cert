From PlutusCert Require Import
  PlutusIR
  Util
  Congruence
  .
Import NamedTerm.

From Coq Require Import
  Lists.List
  Strings.String.
Import ListNotations.

(*

Transforms (repeated) β-redexes into let nonrec

         $₃
       /  \
     $₂    t₃
   /  \
  $₁   t₂
/  \                    =>      let nonrec x = t₁
λx t₁                                      y = t₂
|                                          z = t₃
λy                              in t_body
|
λz
|
t_body

*)

Inductive collect_args : Term -> list Term -> Term -> Prop :=

  | ca_Apply : forall t_f t_x args t_inner_f,
      collect_args t_f             (t_x :: args) t_inner_f ->
      collect_args (Apply t_f t_x) args          t_inner_f

  | ca_Other : forall t,
  (* ~ (exists t_f t_x, t = Apply t_f t_x) -> *) (* enforces the longest sequence of arguments *)
      collect_args t [] t
.

Inductive collect_binders : Term -> list VDecl -> Term -> Prop :=

  | cv_LamAbs : forall t_body vdecls v ty t_inner,
      collect_binders t_body               vdecls t_inner ->
      collect_binders (LamAbs v ty t_body) (VarDecl v ty :: vdecls) t_inner

  | cv_Other : forall t,
  (* ~ (exists v ty t', t = LamAbs v ty t') -> *) (* enforces the longest sequence of lambda binders *)
      collect_binders t [] t
.

Reserved Notation "t₁ ▷-β t₂" (at level 30).
Inductive extract_bindings : Term -> Term -> Prop :=

  | eb_collect_Apply : forall t₁ t₂ args vdecls t_inner_f t_inner,
      collect_args t₁ args t_inner_f ->
      is_cons args ->
      collect_binders t_inner_f vdecls t_inner ->
      is_cons vdecls ->
      t_inner ▷-β t₂ ->
    (* -------------------------------- *)
      t₁ ▷-β Let NonRec (zip_with (TermBind Strict) (rev vdecls) args) t₂

  | eb_TyInst_TyAbs : forall ty v k t_body,

    (* ------------------------------ *)
      TyInst (TyAbs v k t_body) ty
        ▷-β
      Let NonRec [TypeBind (TyVarDecl v k) ty] t_body

  | eb_Cong : forall t1 t2,
      Cong extract_bindings t1 t2 ->
    (* ------------------------------ *)
      t1 ▷-β t2

where "t1 ▷-β t2" := (extract_bindings t1 t2)
.


Definition is_extract_bindings : Term -> Term -> bool.
Admitted.

Lemma is_extract_bindings_sound : forall t₁ t₂,
  is_extract_bindings t₁ t₂ = true -> extract_bindings t₁ t₂.
Admitted.

(*
Possible alternative formulation (small step)
---

Extract one binding at a time:

  Inductive extract_binding : Term -> Term -> Prop :=

    | eb_Apply_LamAbs : forall v ty t_body t_arg,
        extract_binding
        (Apply (LamAbs v ty t_body) t_arg)
        (Let NonRec [TermBind Strict (VarDecl v ty) t_arg] t_body)


    | extract_binding_cong : forall
        Cong extract_binding t₁ t₂ ->
        extract_binding t₁ t₂
  .

Then take the transitive closure of extract_binding.

Then relate through LetMerge (all steps produce a binding group with single binding)

*)
