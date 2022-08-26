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
  Lists.List
  Lists.ListSet
  Strings.String
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

Inductive collect_binding_groups : Term -> list binding_group -> Term -> Prop :=
  | cv_Let : forall t_body lets t_inner r bs,
      collect_binding_groups t_body lets t_inner ->
      collect_binding_groups (Let r bs t_body) ((r, bs) :: lets) t_inner
  | cv_Other : forall t_inner,
      collect_binding_groups t_inner [] t_inner
  .

Reserved Notation "t₁ ▷-split_syn t₂" (at level 30).
Inductive split_syn : Term -> Term -> Prop :=
  | split_rec_let : forall bs t_body t bgs t_inner,

      collect_binding_groups t bgs t_inner ->
      list_eq_elems bs (List.concat (map snd bgs)) ->
      (*------------------------------------*)
      (Let Rec bs t_body) ▷-split_syn t

  | split_rec_cong : forall t t',
      Cong split_syn t t' ->
      (*--------------------*)
      t ▷-split_syn t'
where
  "t1 ▷-split_syn t2" := (split_syn t1 t2)
.


Definition split_rec t t' :=
  t ▷-split_syn t' /\
  exists ty, (empty ,, empty |-+ t' : ty) /\
  unique t'.


Definition collect_binding_groups_dec
     : Term -> list binding_group * Term.
Admitted.

(* Note, the below is unnecessary and implied by has_type *)
(*
Definition well_scoped (Γ : list string) (bg : binding_group) : Prop :=
  match bg with
    | (rec, bs) => forall b, In b bs ->
        exists s v t, b = TermBind s v t /\
          match rec with

            | Rec    =>
                incl (set_diff string_dec (free_vars String.eqb t) Γ)
                     (free_vars_bindings String.eqb (free_vars_binding String.eqb) Rec bs)

            | NonRec =>
                exists bs_pre bs_post, bs = bs_pre ++ b :: bs_post /\
                incl (free_vars_binding String.eqb NonRec b)
                     (Γ ++ bound_vars_bindings bs_pre)
          end
  end.

Fixpoint well_scoped_groups (Γ : list string) (bgs : list binding_group) : Prop :=
  match bgs with
    | []          => True
    | (bg :: bgs) => well_scoped Γ bg /\ well_scoped_groups (bound_vars_bindings (snd bg) ++ Γ) bgs
  end.

Definition same_bindings (bs : list Binding) (groups : list binding_group) : Prop :=
  let bs' := concat (map snd groups) in
  NoDup bs ->
  NoDup bs' ->
  list_same_elems bs bs'.



Inductive split_rec_let : list string -> binding_group -> list binding_group -> Prop :=
  | srl : forall Γ bs groups,
    
    same_bindings bs groups ->
    split_rec_let bs groups

*)

