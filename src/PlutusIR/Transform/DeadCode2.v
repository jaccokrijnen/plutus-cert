From Coq Require Import
  Strings.String
  Lists.List
  Utf8_core
.

From PlutusCert Require Import
  PlutusIR
  PlutusIR.Analysis.FreeVars
  PlutusIR.Analysis.BoundVars
  PlutusIR.Analysis.Purity
  PlutusIR.Analysis.UniqueBinders
  PlutusIR.Transform.Compat
.

Import NamedTerm.
Import UniqueBinders.
Import ListNotations.

Definition fv : Term -> list string := Term.fv.
Definition ftv : Term -> list string := Term.ftv.

Definition disjoint {A} (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.

Definition unused_in (b : Binding) (t : Term) : Prop :=
  disjoint (bvb b) (fv t) /\
  disjoint (btvb b) (ftv t)
.

Inductive dc : Term -> Term -> Prop :=
  | dc_compat
      (t t'     : Term)
      (H_compat : Compat dc t t')
      : dc t t'

    (* Note: This compat case includes a case for Let, which are already
    covered by the following four constructors (e.g. there is more than one way
    to prove compatibility with let). If we change this, there should be `compat`
    constructors for each of the other AST constructor *)

  | dc_delete_binding
      b bs t t'
      (H_pure : pure_binding [] b)          (* Syntactic approximation of a pure (terminating) binding *)
      (H_unused : unused_in b t')           (* its bound variables do not occur free in the post-term *)
      (H_dc_bs : dc (Let NonRec bs  t) t')
      : dc (Let NonRec (b :: bs) t) t'

  | dc_keep_binding
      b b' bs bs' t t'
      (H_dc_b : Compat_Binding dc b b')
      (H_dc_bs : dc (Let NonRec bs t) (Let NonRec bs'  t'))
      : dc (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')


  (* This rule allows for deleting the whole binding group *)
  | dc_delete_let_nil
      t t'
      (H_dc_t : dc t t')
      : dc (Let NonRec [] t) t'

  | dc_compat_let_nil_nil
      t t'
      (H_dc_t : dc t t')
      : dc (Let NonRec [] t) (Let NonRec [] t')

  | dc_letrec
      bs bs' t t'
      (H_dc_rec : dc_rec bs' (Let Rec bs t) (Let Rec bs' t'))
      : dc (Let Rec bs t) (Let Rec bs' t')

with dc_rec : list Binding -> Term -> Term -> Prop :=

  (*
  Note: dc_rec does not include the possibility for the whole group to be
  removed like for NonRec in dc.

  This is because a rule like dc_rec_delete_binding needs to check if the bound
  variables are unused in a specific term: Let Rec bs0 t' (where bs0 are the
  complete set of bindings in the let-rec). In the non-recursive case (where
  let-scoping is linear), we can just check unusedness in the post-term
  (regardless of its structure, therefore allowing a term where the complete let
  was removed).
  *)

  | dc_rec_delete_binding
      b bs bs' bs'0 t t'
      (H_pure : pure_binding [] b)
      (H_unused : unused_in b (Let Rec bs'0 t'))
      (H_dc_bs : dc_rec bs'0 (Let Rec bs t) (Let Rec bs' t'))
      : (*-------------------------------------------------*)
      dc_rec bs'0 (Let Rec (b :: bs) t) (Let Rec bs' t')

  | dc_rec_keep_binding
      b b' bs bs' bs'0 t t'
      (H_dc_b : Compat_Binding dc b b')
      (H_dc_bs : dc_rec bs'0 (Let Rec bs t) (Let Rec bs' t'))
      : (*-------------------------------------------------*)
      dc_rec  bs'0 (Let Rec (b :: bs) t) (Let Rec (b' :: bs') t')

  | dc_rec_compat_let_nil_nil
      t t' bs'0
      (H_dc_t : dc t t')
      : (*---------------*)
      dc_rec bs'0 (Let Rec [] t) (Let Rec [] t')
.

Scheme dc__ind := Minimality for dc Sort Prop.

Open Scope type_scope.

Definition dead_code t t' := unique_tm t * dc t t'.

Lemma dc_sym : ∀ t, dc t t.
Admitted.
