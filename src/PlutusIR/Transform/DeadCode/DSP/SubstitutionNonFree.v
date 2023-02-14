From Coq Require Import
  List
  Strings.String
  Lia
  Program.Equality
.

From PlutusCert Require Import Semantics.Dynamic.
From PlutusCert Require Import Semantics.Static.
From PlutusCert Require Import Transform.DeadCode.
From PlutusCert Require Import Analysis.WellScoped.
From PlutusCert Require Import TypeSafety.TypeLanguage.Preservation.
From PlutusCert Require Import SemanticEquivalence.LogicalRelation.
From PlutusCert Require Import FreeVars.
From PlutusCert Require Import Purity.

Import ListNotations.
Import UniqueBinders.
Import Utf8_core.

Set Diffs "on".

Section Term.

  Import FreeVars.Term.

  Definition fv : Term -> list string := (Term.fv string_dec).
  Definition ftv : Term -> list string := (Term.ftv string_dec).
  Definition fv_binding : Recursivity -> Binding -> list string := (Term.fvb string_dec).
  Definition fv_bindings : Recursivity -> list Binding -> list string := (Term.fvbs string_dec fv_binding).


  Lemma not_in_app : ∀ A (x : A) xs xs',
    x ∉ (xs ++ xs') ->
    x ∉ xs /\ x ∉ xs'.
  Proof.
    intros A x xs xs' H_notin.
    induction xs as [ | x' xs].
    all: split; auto.
    - cbn - [In] in H_notin.
      apply not_in_cons in H_notin as [H_x_x' H_xs_xs'].
      apply IHxs in H_xs_xs' as [ ].
      apply not_in_cons.
      auto.
    - eapply proj2.
      apply IHxs.
      cbn - [In] in H_notin.
      apply not_in_cons in H_notin.
      destruct H_notin; eauto.
  Qed.

  Lemma not_in_fv_TyAbs x v k t :
    x ∉ fv (TyAbs k v t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_LamAbs x y ty t :
    x ∉ fv (LamAbs y ty t) ->
    (x =? y)%string = false -> (* TODO, require x ≠ y, either in bool or prop form *)
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Apply_l x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Apply_r x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t'.
  Admitted.


  Lemma not_in_fv_Constant x c :
    x ∉ fv (Constant c).
  Admitted.

  Lemma not_in_fv_Builtin x f :
    x ∉ fv (Builtin f).
  Admitted.

  Lemma not_in_fv_TyInst x t ty :
    x ∉ fv (TyInst t ty) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Error x ty :
    x ∉ fv (Error ty).
  Admitted.

  Lemma not_in_fv_IWrap x ty1 ty2 t:
    x ∉ fv (IWrap ty1 ty2 t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Unwrap x t :
    x ∉ fv (Unwrap t) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_TermBind x r s y ty t:
    x ∉ fv_binding r (TermBind s (VarDecl y ty) t) ->
    False ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Let_NonRec_t x r bs t :
    x ∉ fv (Let r bs t) ->
    existsb (eqb x) (bvbs bs) = false ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_fv_Let_NonRec_b x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    x ∉ fv_binding NonRec b.
  Admitted.

  Lemma not_in_fv_Let_NonRec_bs x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    existsb (eqb x) (bvb b) = false ->
    x ∉ fv (Let NonRec bs t).
  Admitted.

  Create HintDb not_in.
  Hint Resolve
    not_in_fv_TyAbs 
    not_in_fv_LamAbs
    not_in_fv_Apply_l
    not_in_fv_Apply_r
    not_in_fv_Constant
    not_in_fv_Builtin
    not_in_fv_TyInst
    not_in_fv_Error
    not_in_fv_IWrap
    not_in_fv_Unwrap
    : not_in.

  Lemma fv_let_cons x b bs t :
    (x ∈ fv (Let NonRec bs t)) ->
    (x ∈ fv (Let NonRec (b :: bs) t)).
  Admitted.

  Definition P_Term t := forall x t',
    x ∉ fv t ->
    subst x t' t = t.

  Definition P_Binding b := forall r x t',
    x ∉ fv_binding r b ->
    subst_b x t' b = b.

  Lemma existsb_bvbs_bs x (b : Binding) bs :
    existsb (eqb x) (bvbs (b :: bs)) = true ->
    existsb (eqb x) (bvb b) = false ->
    existsb (eqb x) (bvbs bs) = true.
  Proof.
    intros H_in_bvbs H_not_in_bvb.
              unfold bvbs in H_in_bvbs.
              simpl in H_in_bvbs.
              rewrite existsb_app in H_in_bvbs.
              rewrite Bool.orb_true_iff in H_in_bvbs.
              destruct H_in_bvbs.
              **
                 rewrite H in H_not_in_bvb.
                 inversion H_not_in_bvb.
              ** eauto.
  Qed.

  Lemma existsb_In x xs :
    existsb (eqb x) xs = true ->
    x ∈ xs.
  Proof.
    intros H_ex.
    induction xs.
    - inversion H_ex.
    - destruct (string_dec x a); subst.
      + apply in_eq.
      + 
        apply existsb_exists in H_ex as [].
        destruct H.
        apply eqb_eq in H0; subst.
        assumption.
  Qed.

  Lemma existsb_not_in x xs :
    existsb (eqb x) xs = false ->
    x ∉ xs.
  Proof.
  Admitted.


  Lemma subst_br_not_in_fv x t' bs t :
    x ∉ fv (Let Rec bs t) ->
    Util.ForallP P_Binding bs ->
    existsb (eqb x) (bvbs bs) = false ->
    subst_br x t' bs = bs.
  Proof.
  Admitted.

  Lemma subst_bnr_not_in_fv x t' bs t:
    x ∉ fv (Let NonRec bs t) ->
    Forall P_Binding bs ->
    subst_bnr x t' bs = bs.
  Proof.
    intros H_not_in_fv H_bs.
    induction bs as [ | b bs].
    - reflexivity.
    - simpl.
      destruct (existsb (eqb x) (bvb b)) eqn:H_in_bvb.
      all: inversion H_bs; subst.
      + apply not_in_fv_Let_NonRec_b in H_not_in_fv.
        f_equal.
        eauto.
      + (* x must be bound in bs *)
        f_equal.
          * apply not_in_fv_Let_NonRec_b in H_not_in_fv.
            eauto.
          *
          destruct (existsb (eqb x) (bvbs bs)) eqn:H_ex_bvbs. 
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using not_in_fv_Let_NonRec_bs.
               eauto using existsb_bvbs_bs.
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using  not_in_fv_Let_NonRec_bs.
               assert (x ∉ bvbs bs). {
                 apply existsb_not_in in H_ex_bvbs.
                 assumption.
               }
               eauto.
  Qed.


  Lemma subst_not_in_fv : forall t, P_Term t.
  Proof.
    apply Term__multind with (P := P_Term) (Q := P_Binding).

    all: try (
      unfold P_Term in *;
      intros;
      rewrite subst_equation;
      f_equal;
      eauto with not_in
   ).

    (* Let *)
    - destruct rec; destruct (existsb (eqb x) (bvbs bs)) eqn:H_existsb.

      (* Let NonRec *)
      + (* x does not occur free, but is shadowed in bs *)
        f_equal.
        rewrite subst_bnr'_equation.
        induction bs.
        * reflexivity.
        * destruct (existsb (eqb x) (bvb a)) eqn:H_exists_here.
          ** inversion H. subst. unfold P_Binding in H4.
             apply not_in_fv_Let_NonRec_b in H1.
             f_equal.
             f_equal.
             eauto.
          ** f_equal.
              ***
                  apply not_in_fv_Let_NonRec_b in H1.
                  inversion H. subst. unfold P_Binding in H4.
                  eauto.
              *** inversion H; subst. rewrite Util.ForallP_Forall in H5.
                  eauto using subst_bnr_not_in_fv, existsb_bvbs_bs, not_in_fv_Let_NonRec_bs.

      (* Let NonRec *)
      + (* x does not occur free and is also not bound in bs *)
        f_equal.
        rewrite Util.ForallP_Forall in H.
        * eapply subst_bnr_not_in_fv with (t := t); eauto.
        * assert (x ∉ fv t). {
            apply not_in_fv_Let_NonRec_t in H1; eauto.
            }
          eauto.
      + reflexivity.
      + f_equal.
        * eapply subst_br_not_in_fv with (t := t); eauto.
        * eapply not_in_fv_Let_NonRec_t in H1; eauto.

    (* Var *)
    - simpl in H.
      destruct (x =? s)%string eqn:H_eqb.
      + apply eqb_eq in H_eqb.
        apply eq_sym in H_eqb.
        assert False. auto.
        contradiction.
      + reflexivity.

    (* LamAbs *)
    -
      destruct (x =? s)%string eqn:H_eqb.
      + reflexivity.
      + f_equal; eauto with not_in.

    (* TermBind *)
    - unfold P_Term, P_Binding.
      intros.
      rewrite subst_b_equation.
      destruct v as [y ty].
      destruct (x =? y)%string eqn:H_eqb.
      + unfold fv_binding in *.
        destruct r.
        rewrite fvb_equation in H0.
        *
          f_equal.
          eauto.
        * f_equal.
          rewrite eqb_eq in H_eqb. subst.
      f_equal.
      unfold fv_binding in H0.
      rewrite fvb_equation in H0.
      admit.
      + admit.

    (* TypeBind *)
    - unfold P_Binding.
      reflexivity.

    (* DatatypeBind *)
    - unfold P_Binding.
      reflexivity.
Admitted.



End Term.
