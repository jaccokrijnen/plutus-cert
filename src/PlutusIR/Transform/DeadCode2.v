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
  Util
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


Section Compatibility.

  Context {A : Type}.
  Context (R : A -> A -> Prop).

  Definition R_refl (t : A) : Prop :=
    R t t.

  Definition compat_1 (f : A -> A) : Prop :=
    forall t t', R t t' -> R (f t) (f t')
  .

  Definition compat_2 (f : A -> A -> A) : Prop :=
    forall s s' t t',
      R s s' ->
      R t t' ->
      R (f s t) (f s' t')
  .

End Compatibility.

Inductive dc : Term -> Term -> Prop :=
  | dc_Var n :
      R_refl dc (Var n)
  | dc_TyAbs X k :
      compat_1 dc (TyAbs X k)
  | dc_LamAbs x T:
      compat_1 dc (LamAbs x T)
  | dc_Apply :
      compat_2 dc Apply
  | dc_Constant k :
      R_refl dc (Constant k)
  | dc_Builtin f :
      R_refl dc (Builtin f)
  | dc_TyInst T :
      compat_1 dc (fun t => TyInst t T)
  | dc_Error T :
      R_refl dc (Error T)
  | dc_IWrap F T :
      compat_1 dc (IWrap F T)
  | dc_Unwrap :
      compat_1 dc (Unwrap)
  | dc_Constr_nil n :
      dc (Constr n nil) (Constr n nil)
  | dc_Constr_cons n t t' ts ts' :
      dc t t' ->
      dc (Constr n ts) (Constr n ts') ->
      dc (Constr n (t :: ts)) (Constr n (t' :: ts'))
  | dc_Case_nil d d':
      dc d d' ->
      dc (Case d []) (Case d' [])
  | dc_Case_cons d d' t t' ts ts' :
      dc (Case d ts) (Case d' ts) ->
      dc (Case d (t :: ts)) (Case d' (t' :: ts'))

    (* Note: This compat case includes a case for Let, which are already
    covered by the following four constructors (e.g. there is more than one way
    to prove compatibility with let). If we change this, there should be `compat`
    constructors for each of the other AST constructor *)

  | dc_Let_NonRec
      bs bs' t t'
      (H_dc : dc t t')
      (H_dc_NonRec : dc_NonRec t' bs bs' )
      :
      dc (Let NonRec bs t) (Let NonRec bs' t')

  | dc_Let_Rec
      bs bs' t t'
      (H_dc : dc t t')
      (H_dc_Rec : dc_Rec bs' t' bs bs' )
      :
       dc (Let Rec bs t) (Let Rec bs' t')
with dc_Binding : Binding -> Binding -> Prop :=
  | dc_refl_TermBind s v t :
      R_refl dc_Binding (TermBind s v t)
  | dc_refl_TypeBind tvd T :
      R_refl dc_Binding (TypeBind tvd T)
  | dc_refl_DatatypeBind dtd :
      R_refl dc_Binding (DatatypeBind dtd)
  (* TODO: DatatypeBind with unused constructors/destructor *)

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
      (H_dc_b : dc_Binding b b')
      (H_dc_bs : dc_NonRec t' bs bs')
      :
      dc_NonRec t' (b :: bs) (b' :: bs')

  | dc_NonRec_nil
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

  | dc_Rec_keep
      b b' bs bs' bs'0 t'
      (H_dc_b : dc_Binding b b')
      (H_dc_bs : dc_Rec bs'0 t' bs bs')
      : (*---------------------------------------*)
      dc_Rec bs'0 t' (b :: bs) (b' :: bs')

  | dc_Rec_nil
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

Hint Unfold R_refl.

Lemma dc_sym : ∀ t, dc t t.
Proof.
  apply Term__multind with
    (P := fun t => dc t t)
    (Q := fun b => dc_Binding b b)
  .
  all: try constructor.
  all: try assumption.
  - intros rec bs t IH_bs H_dc.
    rewrite ForallP_Forall in *.
    destruct rec.
    + constructor.
      * assumption.
      * induction bs.
        ** constructor.
        ** apply dc_NonRec_keep.
          *** apply Forall_inv in IH_bs.
             assumption.
          *** apply Forall_inv_tail in IH_bs.
             auto.
    + constructor.

      * assumption.
      *
        (* Forget about bs in the first argument of dc_Rec,
         before doing induction *)
        assert (H_bs0 : exists bs0, bs = bs0). exists bs. reflexivity. destruct H_bs0.
        rewrite H at 1.
        clear H.

        induction bs.
        ** econstructor. eassumption.
        ** apply dc_Rec_keep.
          *** apply Forall_inv in IH_bs.
             assumption.
          *** apply Forall_inv_tail in IH_bs.
             auto.
  - (* Constr *)
    intros.
    induction ts.
    + constructor.
    + apply dc_Constr_cons.
      *
        rewrite ForallP_Forall in H.
        apply Forall_inv in H.
        assumption.
      * rewrite ForallP_Forall in *.
        apply Forall_inv_tail in H.
          auto.
  - (* Case *)
    intros.
    induction ts.
    + constructor.
      assumption.
    + apply dc_Case_cons.
      rewrite ForallP_Forall in *.
      apply Forall_inv_tail in H0.
      auto.
Qed.
