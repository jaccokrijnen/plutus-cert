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


Section Term.

  Import FreeVars.Term.

  Definition fv : Term -> list string := Term.fv.
  Definition ftv : Term -> list string := Term.ftv.
  Definition fv_binding : Recursivity -> Binding -> list string := Term.fvb.
  Definition fv_bindings : Recursivity -> list Binding -> list string := Term.fvbs fv_binding.


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

  Lemma not_in_fv_Constr x i ts :
    x ∉ fv (Constr i ts) ->
    Forall (fun t => x ∉ fv t) ts.
  Admitted.

  Lemma not_in_fv_Case_1 x t ts :
    x ∉ fv (Case t ts) ->
    Forall (fun t => x ∉ fv t) ts.
  Admitted.

  Lemma not_in_fv_Case_2 x t ts :
    x ∉ fv (Case t ts) ->
    x ∉ fv t.
  Admitted.

  Lemma not_in_remove x xs y :
    x ∉ remove string_dec y xs->
    x <> y ->
    x ∉ xs.
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
    not_in_fv_Constr
    not_in_fv_Case_1
    not_in_fv_Case_2
    : not_in.

  Lemma fv_let_cons x b bs t :
    (x ∈ fv (Let NonRec bs t)) ->
    (x ∈ fv (Let NonRec (b :: bs) t)).
  Admitted.

  Definition P_Term t := forall x t',
    x ∉ fv t ->
    subst x t' t = t.

  Definition P_Binding b := forall r x t',
    (r = Rec -> x ∉ bvb b) -> (* See Note [Assumption of subst_b] *)
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
        unfold P_Binding in H1.
        eapply H1; eauto.
        inversion 1.
      + (* x must be bound in bs *)
        f_equal.
          * apply not_in_fv_Let_NonRec_b in H_not_in_fv.
            eapply H1; eauto.
            inversion 1.
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



  Lemma subst_terms_not_in_fv x t ts :
    Forall P_Term ts ->
    Forall (fun t => x ∉ fv t) ts ->
    map (subst x t) ts = ts.
  Admitted.

  Ltac destruct_if :=
        match goal with
          | |- context[if ?X then _ else _] => destruct X eqn:H_eqb
        end.

  Ltac destruct_match :=
        match goal with
        | |- context[match ?X with | _ => _ end] => destruct X eqn:H_match
        end.

  Lemma subst_not_in_fv : forall t, P_Term t.
  Proof.
    apply Term__multind with (P := P_Term) (Q := P_Binding).
    all: unfold P_Term, P_Binding in *; intros.
    all: try rewrite Util.ForallP_Forall in *.
    all: try rewrite subst_unfold.
    all: try rewrite subst_b_unfold.

    (* Let *)
    -
      destruct_match.
      all: destruct_if.

      (* Let NonRec *)
      + (* x is shadowed in bs *)
        f_equal.
        apply subst_bnr_not_in_fv with (t := t); eauto.
      + (* x is not bound in bs *)
        f_equal.
        * eapply subst_bnr_not_in_fv with (t := t); eauto.
        * apply not_in_fv_Let_NonRec_t in H1; eauto.

      (* Let Rec *)
      + (* x is shadowed in bs *)
        reflexivity.
      + f_equal.
        * eapply subst_br_not_in_fv with (t := t); eauto.
          rewrite Util.ForallP_Forall in *. assumption.
        * eapply not_in_fv_Let_NonRec_t in H1; eauto.

    (* Var *)
    -
      destruct_if.
      +
        apply eqb_eq in H_eqb.
        apply eq_sym in H_eqb.
        simpl in H.
        tauto.
      + reflexivity.

    - (* TyAbs *)
      f_equal.
      eauto with not_in.

    - (* LamAbs *)
      destruct_if.
      + reflexivity.
      + f_equal.
        eapply H.

        (* debug eauto with not_in. *) (* Keeps a shelved var for some reason *)
        eauto using not_in_fv_LamAbs.

    - (* Apply *)
      f_equal; eauto with not_in.

    - (* Constant *)
      reflexivity.

    - (* Builtin *)
      reflexivity.

    - (* TyInst *)
      f_equal; eauto with not_in.

    - (* Error *)
      reflexivity.

    - (* IWrap t *)
      f_equal; eauto with not_in.

    - (* Unwrap *)
      f_equal; eauto with not_in.

    - (* Constr *)
      f_equal; eauto with not_in.
      eapply subst_terms_not_in_fv.
      + assumption.
      + eauto using not_in_fv_Constr.

    - (* Case *)
      f_equal.  eauto with not_in.
      eapply  subst_terms_not_in_fv;
      eauto with not_in.

    - (* TermBind *)
      destruct_match.
      f_equal.
      rewrite fvb_equation in *.
      destruct r.
      + auto.
      +  (* Rec *)
        specialize (H0 eq_refl). (* See Note [Assumption of subst_b] *)
        simpl in H0.
        apply H.

        eauto.
        eapply not_in_remove in H1.
        * assumption.
        * unfold not in *.
          auto.


    - (* TypeBind *)
      unfold P_Binding.
      reflexivity.

    - (* DatatypeBind *)
      unfold P_Binding.
      reflexivity.
Qed.



End Term.
