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
Import UniqueBinders.Term.
Import ListNotations.

Definition fv : Term -> list string := Term.fv string_dec.
Definition ftv : Term -> list string := Term.ftv string_dec.

Definition disjoint {A} (xs ys : list A) : Prop :=
  Forall (fun v => ~ In v ys) xs.


Inductive dc : Term -> Term -> Type :=
  | dc_compat : ∀ t t',
      Compat dc t t' ->
      dc t t'

      (* Note: This includes a case for Let, which are already covered by the following
         four constructors. If we change this, there should be `compat` constructors for each of the
         other AST constructor *)


  | dc_delete_binding : ∀ b bs t t',

      (* Syntactic approximation of a pure binding *)
      pure_binding [] b ->

      (* Its bound variables do not occur free in the post-term *)
      disjoint (bvb b) (fv t') ->
      disjoint (btvb b) (ftv t') ->

      dc (Let NonRec       bs  t) t' ->
      dc (Let NonRec (b :: bs) t) t'

  | dc_keep_binding : ∀ b b' bs bs' t t',
      dc t t' ->
      Compat_Binding dc b b' ->
      dc (Let NonRec       bs  t) (Let NonRec        bs'  t') ->
      dc (Let NonRec (b :: bs) t) (Let NonRec (b' :: bs') t')

  | dc_delete_let_nil : ∀ t t',
      dc             t  t' ->
      dc (Let NonRec [] t) t'

  | dc_compat_let_nil_nil : ∀ NonRec t t',
      dc             t              t' ->
      dc (Let NonRec [] t) (Let NonRec [] t').

  (* TODO: support Let Rec (See #42) *)

Open Scope type_scope.

Definition dead_code t t' := unique t * dc t t'.

Lemma dc_sym : ∀ t, dc t t.
Admitted.
