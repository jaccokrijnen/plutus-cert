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
      :
      dc t t'

    (* Note: This compat case includes a case for Let, which are already
    covered by the following four constructors (e.g. there is more than one way
    to prove compatibility with let). If we change this, there should be `compat`
    constructors for each of the other AST constructor *)

  | dc_Let_NonRec
      bs bs' t t'
      (H_dc_NonRec : dc_NonRec t' bs bs' )
      :
      dc (Let NonRec bs t) (Let NonRec bs' t')

  | dc_Let_Rec
      bs bs' t t'
      (H_dc_Rec : dc_Rec bs' t' bs bs' )
      :
       dc (Let Rec bs t) (Let Rec bs' t')

with dc_NonRec : Term -> list Binding -> list Binding -> Prop :=
  | dc_NonRec_elim
      b bs bs' t'
      (H_pure : pure_binding [] b)          (* Syntactic approximation of a pure (terminating) binding *)
      (H_unused : unused_in b (Let NonRec bs' t'))  (* its bound variables do not occur free in the post-term *)
      (H_dc_bs : dc_NonRec t' bs bs')
      :
      dc_NonRec t' (b :: bs) bs'

  | dc_NonRec_keep
      b b' bs bs' t'
      (H_dc_b : Compat_Binding dc b b')
      (H_dc_bs : dc_NonRec t' bs bs')
      :
      dc_NonRec t' (b :: bs) (b' :: bs')

  | dc_NonRec_compat_let_nil_nil
      t'
      : (*------------*)
      dc_NonRec t' [] []

with dc_Rec : list Binding -> Term -> list Binding -> list Binding -> Prop :=

  | dc_Rec_elim
      b bs bs' bs'0 t'
      (H_pure : pure_binding [] b)
      (H_unused : unused_in b (Let Rec bs'0 t'))
      (H_dc_bs : dc_Rec bs'0 t' bs bs')
      :
      dc_Rec bs'0 t' (b :: bs) bs'

  | dc_Rec_keep_binding
      b b' bs bs' bs'0 t'
      (H_dc_b : Compat_Binding dc b b')
      (H_dc_bs : dc_Rec bs'0 t' bs bs')
      : (*---------------------------------------*)
      dc_Rec bs'0 t' (b :: bs) (b' :: bs')

  | dc_Rec_compat_let_nil_nil
      t t' bs'0
      (H_dc_t : dc t t')
      : (*------------*)
      dc_Rec bs'0 t' [] []
.

Scheme dc__ind := Minimality for dc Sort Prop
  with dc_NonRec__ind := Minimality for dc_NonRec Sort Prop
  with dc_Rec__ind := Minimality for dc_Rec Sort Prop
.

Combined Scheme dc__multind from
  dc__ind,
  dc_NonRec__ind,
  dc_Rec__ind.

Lemma dc_sym : ∀ t, dc t t.
Admitted.
