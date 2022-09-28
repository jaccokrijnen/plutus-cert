From PlutusCert Require Import
  PlutusIR
  Analysis.FreeVars
  Analysis.Equality
  Analysis.UniqueBinders
  Transform.Congruence
  Static.Typing
  .
Import NamedTerm.
Import Term.

From Coq Require Import
  Strings.String
  Lists.List
  Lists.ListSet
  .
Import ListNotations.

(* A binding group (Let without a body) *)
Definition binding_group := (Recursivity * list Binding)%type.

(*
Assuming globally unique variables, the new binding groups much satisfy:
  - Well-scoped: each free variable in a binding RHS is bound
  - All bindings equals those in the let-rec before transformaton

Note that strictness of bindings does not matter: if one of the (strict)
bindings diverges, the whole let-block diverges. This behaviour remains when
regrouping/reordering all bindings.
*)

Definition list_eq_elems {A} xs ys : Prop :=
  forall (x : A), In x xs <-> In x ys.

(* Collect subsequent binding groups, together with the "inner" term *)
Inductive collect_binding_groups : Term -> list binding_group -> Term -> Prop :=

  | cv_Let : forall t_body lets t_inner r bs,
      collect_binding_groups t_body lets t_inner ->
      collect_binding_groups (Let r bs t_body) ((r, bs) :: lets) t_inner

  | cv_Other : forall t_inner,
      collect_binding_groups t_inner [] t_inner

  .

Inductive split_syn : Term -> Term -> Prop :=
  | split_rec_let : forall bs t_body t bgs t_inner,

      (* a decision-procedure would need to find the list bgs of binding groups that
         satisfies the second premise (needs to do backtracking) *)
      collect_binding_groups t bgs t_inner ->
      list_eq_elems bs (concat (map snd bgs)) ->
      split_syn t_body t_inner ->
      split_syn (Let Rec bs t_body) t

  | split_rec_cong : forall t t',
      Cong split_syn t t' ->
      split_syn t t'
.

(* TODO: define and use well_scoped instead of well_typed *)
Definition split_rec t t' :=
  split_syn t t' /\
  well_typed t' /\
  unique t.


Definition collect_binding_groups_dec
     : Term -> list binding_group * Term.
Admitted.
