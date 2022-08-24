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

Inductive collect_args : Term -> list Term -> list Binding -> Term -> Prop :=

  | ca_LamAbs : forall t_body t_arg args binds t_inner_body v ty,
      collect_args t_body               args            binds                                           t_inner_body ->
      collect_args (LamAbs v ty t_body) (t_arg :: args) (TermBind Strict (VarDecl v ty) t_arg :: binds) t_inner_body

  | ca_Apply : forall t_f t_x args binds t_body,
      collect_args t_f             (t_x :: args) binds t_body ->
      collect_args (Apply t_f t_x) args          binds t_body

.


Reserved Notation "t₁ ▷-β t₂" (at level 30).
Inductive extract_bindings : Term -> Term -> Prop :=

  | ca_collect : forall t₁ t₂ binds t_inner,
      collect_args t₁ [] binds t_inner ->
      is_cons binds ->
      t_inner ▷-β t₂ ->
      t₁ ▷-β Let NonRec (rev binds) t₂

  | ca_cong : forall t1 t2,
      Cong extract_bindings t1 t2 ->
      t1 ▷-β t2

where "t1 ▷-β t2" := (extract_bindings t1 t2)
.


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
