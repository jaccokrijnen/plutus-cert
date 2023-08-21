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


Inductive dc : Term -> Term -> Prop :=
  | dc_compat : ∀ t t',
      Compat dc t t' ->
      dc t t'

      (* Note: there is another way to relate `Let` groups that have no bindings
         removed, by using dc_keep_binding and dc_compat_let_nil_nil
         If we change this, there should be `compat` constructors for each of the
         other AST constructor *)


  | dc_delete_binding : ∀ rec b bs t t',

      (* Syntactic approximation of a pure binding *)
      pure_binding [] b ->

      (* Its bound variables do not occur free in the post-term *)
      disjoint (bvb b) (fv t') ->
      disjoint (btvb b) (ftv t') ->

      dc (Let rec       bs  t) t' ->
      dc (Let rec (b :: bs) t) t'

  | dc_keep_binding : ∀ rec b b' bs bs' t t',
      dc t t' ->
      dc_binding b b' ->
      dc (Let rec       bs  t) (Let rec        bs'  t') ->
      dc (Let rec (b :: bs) t) (Let rec (b' :: bs') t')

  | dc_delete_let_nil : ∀ rec t t',
      dc             t  t' ->
      dc (Let rec [] t) t'

  | dc_compat_let_nil_nil : ∀ rec t t',
      dc             t              t' ->
      dc (Let rec [] t) (Let rec [] t')


with dc_binding : Binding -> Binding -> Prop :=

  | dc_TermBind : ∀ s vd t t',
      dc t t' ->
      dc_binding (TermBind s vd t) (TermBind s vd t')

  | dc_TypeBind : ∀ tvd ty,
      dc_binding (TypeBind tvd ty) (TypeBind tvd ty)

  | dc_DatatypeBind : ∀ dtd,
      dc_binding (DatatypeBind dtd) (DatatypeBind dtd)
.


Definition dead_code t t' := unique t /\ dc t t'.

Lemma dc_sym : ∀ t, dc t t.
Admitted.
