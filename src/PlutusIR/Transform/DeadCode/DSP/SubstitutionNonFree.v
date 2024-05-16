From Coq Require Import
  List
  Lia
  Program.Equality
  Bool.Bool
  Strings.String
.

From PlutusCert Require Import
  PlutusIR
  Dynamic.Substitution
  Analysis.FreeVars
  Analysis.BoundVars
  Analysis.UniqueBinders
  Util.List
  Util.Tactics
.

Import ListNotations.
Import UniqueBinders.
Import Utf8_core.



Section Term.

  Import FreeVars.Term.

  Definition fv : term -> list string := Term.fv.
  Definition ftv : term -> list string := Term.ftv.
  Definition fv_binding : recursivity -> binding -> list string := Term.fvb.
  Definition fv_bindings : recursivity -> list binding -> list string := Term.fvbs fv_binding.

  Lemma remove_unfold {A} eq_dec (x : A) xs :
    remove eq_dec x xs =
    match xs with
    | [] => []
    | y :: tl => if eq_dec x y then remove eq_dec x tl else y :: remove eq_dec x tl
    end.
  Proof.
    destruct xs; reflexivity.
  Qed.

  Lemma cons_app {A} (x : A) xs :
    (x :: xs) = [x] ++ xs.
  Proof.
    reflexivity.
  Qed.


  Lemma bvbs_app (xs ys : list binding) :
    bvbs (xs ++ ys) = bvbs xs ++ bvbs ys.
  Proof.
    unfold bvbs.
    rewrite map_app.
    rewrite concat_app.
    reflexivity.
  Qed.


  Lemma not_in_bvbs_cons (x : string) (b : binding) bs :
    x ∉ bvbs (b :: bs) ->
    x ∉ bvb b /\ x ∉ bvbs bs.
  Proof.
    rewrite cons_app.
    rewrite bvbs_app.
    intros.
    rewrite not_in_app in H.
    unfold bvbs in H.
    simpl in H.
    rewrite app_nil_r in H.
    auto.
  Qed.

  Lemma not_in_bvbs_hd (x : string) (b : binding) bs :
    x ∉ bvbs (b :: bs) ->
    x ∉ bvb b.
  Proof.
    unfold bvbs.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    intuition.
  Qed.

  Lemma not_in_bvbs_tl (x : string) (b : binding) bs :
    x ∉ bvbs (b :: bs) ->
    x ∉ bvbs bs.
  Proof.
    unfold bvbs.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    intuition.
  Qed.

  Lemma not_in_existsb x xs :
    x ∉ xs <-> existsb (eqb x) xs = false.
  Proof.
    split; intros.
    - (* -> *)
      induction xs; auto.
      destruct (string_dec x a).
      + (* x = a *)
        subst a.
        assert (x ∈ (x :: xs)) by intuition.
        contradiction.
      + (* x ≠ a *)
        simpl.
        rewrite orb_false_iff.
        split.
        * rewrite eqb_neq. auto.
        * intuition.
    - (* <- *)
      unfold not. intros H0.
      induction xs; inversion H0.
      + (* x = a *)
        apply eq_sym in H1.
        rewrite <- eqb_eq in H1.
        simpl in H.
        rewrite orb_false_iff in H.
        destruct H as [Heq _].
        apply eq_sym in H1.
        assert (true = false) by eauto using eq_trans.
        inversion H.
      + (* x ≠ a *)
        simpl in H.
        apply orb_false_iff in H as [_ H].
        auto.
  Qed.

  Lemma not_in_remove_many x ys xs :
    x ∉ xs \ ys ->
    x ∉ ys ->
    x ∉ xs.
  Proof.
    intros.
    unfold not.
    intros.
    assert (x ∈ xs \ ys). {
      apply in_remove_many.
      auto.
    }
    auto.
  Qed.

  Lemma not_in_remove_many' x ys xs :
    x ∉ xs ->
    x ∉ xs \ ys.
  Proof.
    unfold not.
    intros.
    apply <- in_remove_many in H0.
    intuition.
  Qed.

  Lemma not_in_in x xs ys :
    x ∉ xs \ ys ->
    x ∈ xs ->
    x ∈ ys.
  Proof.
    intros.
    destruct (in_dec string_dec x ys).
    - auto.
    - assert (x ∈ (xs \ ys)).
      + rewrite <- in_remove_many.
        intuition.
      + intuition.
  Qed.

  Lemma in_not_in x xs ys :
    x ∈ xs ->
    x ∉ ys ->
    x ∈ xs \ ys.
  Proof.
    intros.
    induction ys.
    - auto.
    - rewrite not_in_cons in H0.
      assert (x ∉ [a]). {
        simpl.
        intuition.
      }
      rewrite cons_app.
      rewrite remove_many_app_comm.
      rewrite remove_many_app_r.
      rewrite <- in_remove_many.
      split; intuition.
  Qed.

  Lemma not_in_fv_TyAbs x v k t :
    x ∉ fv (TyAbs k v t) ->
    x ∉ fv t.
  Proof.
    auto.
  Qed.

  Lemma not_in_fv_LamAbs x y ty t :
    x ∉ fv (LamAbs y ty t) ->
    (x =? y)%string = false ->
    x ∉ fv t.
  Proof.
    intros.
    simpl in *.
    rewrite eqb_neq in *.
    unfold not; intros.
    apply H.
    rewrite <- in_remove.
    intuition.
  Qed.

  Lemma not_in_fv_Apply_l x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t.
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Apply_r x t t' :
    x ∉ fv (Apply t t') ->
    x ∉ fv t'.
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Constant x c :
    x ∉ fv (Constant c).
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Builtin x f :
    x ∉ fv (Builtin f).
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_TyInst x t ty :
    x ∉ fv (TyInst t ty) ->
    x ∉ fv t.
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Error x ty :
    x ∉ fv (Error ty).
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_IWrap x ty1 ty2 t:
    x ∉ fv (IWrap ty1 ty2 t) ->
    x ∉ fv t.
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Unwrap x t :
    x ∉ fv (Unwrap t) ->
    x ∉ fv t.
  Proof. simpl. intuition. Qed.

  Lemma not_in_fv_Let_NonRec_t x r bs t :
    x ∉ fv (Let r bs t) ->
    x ∉ bvbs bs ->
    (* existsb (eqb x) (bvbs bs) = false ->*)
    x ∉ fv t.
  Proof.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    destruct H.
    unfold not.
    intros.
    apply H0.
    eapply not_in_in; eauto.
  Qed.

  Lemma not_in_fv_Let_NonRec_hd x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    x ∉ fv_binding NonRec b.
  Proof.
    intros.
    simpl in H.
    rewrite <- app_assoc in H.
    intuition.
  Qed.

  Lemma not_in_fv_Let_NonRec_tl x b bs t :
    x ∉ fv (Let NonRec (b :: bs) t) ->
    x ∉ bvb b ->
    x ∉ fv (Let NonRec bs t).
  Proof.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    destruct H.
    rewrite not_in_app in H.
    destruct H.
    unfold not.
    intros.
    simpl in H3.
    rewrite in_app_iff in H3.
    destruct H3.
    - eapply in_not_in with (ys := bvb b) in H3; auto.
    - apply H1.
      rewrite <- in_remove_many.
      split.
      + rewrite <- in_remove_many in H3.
        intuition.
      + unfold bvbs.
        simpl.
        rewrite not_in_app.
        split;auto.
        rewrite <- in_remove_many in H3.
        intuition.
  Qed.
  

  Lemma not_in_fv_Let_Rec_bs x b bs t :
    x ∉ fv (Let Rec (b :: bs) t) ->
    x ∉ bvbs (b :: bs) ->
    x ∉ fv (Let Rec bs t).
  Proof.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    destruct H.
    apply not_in_remove_many with (xs := fvb Rec b ++ fvbs fvb Rec bs) in H.
    - rewrite not_in_app in H.
      destruct H.
      unfold not.
      intros.
      simpl in H3.
      apply in_app_or in H3.
      destruct H3.
      + intuition.
      + rewrite <- in_remove_many in H3.
        destruct H3.
        apply H1.
        rewrite <- in_remove_many.
        split; auto.
    - unfold not.
      intros.
      rewrite <- in_remove_many in H2.
      destruct H2.
      apply H0.
      eauto using not_in_in.
  Qed.

  Lemma not_in_fv_Let_Rec_head x b bs t :
    x ∉ fv (Let Rec (b :: bs) t) ->
    x ∉ bvbs (b :: bs) ->
    x ∉ fvb Rec b.
  Proof.
    intros.
    simpl in H.
    rewrite not_in_app in H.
    destruct H.
    apply not_in_remove_many with (xs := fvb Rec b ++ fvbs fvb Rec bs) in H.
    - rewrite not_in_app in H.
      intuition.
    - assert (x ∉ (fvb Rec b ++ fvbs fvb Rec bs)).
      { eapply not_in_remove_many.
        + apply H.
        + auto.
      }
      unfold not. intros.
      apply <- in_remove_many in H3.
      intuition.
  Qed.

  Lemma not_in_fv_Constr x i ts :
    x ∉ fv (Constr i ts) ->
    Forall (fun t => x ∉ fv t) ts.
  Proof.
    intros H.
    induction ts; auto.
    simpl in H.
    rewrite not_in_app in H.
    constructor; intuition.
  Qed.

  Lemma not_in_fv_Case_1 x t ts :
    x ∉ fv (Case t ts) ->
    Forall (fun t => x ∉ fv t) ts.
  Proof.
    intros.
    induction ts; auto.
    rewrite fv_equation in H.
    rewrite not_in_app in H.
    destruct H.
    constructor.
    - simpl in H0.
      rewrite not_in_app in H0.
      destruct H0.
      assumption.
    - apply IHts.
      simpl.
      simpl in H0.
      rewrite not_in_app in H0.
      destruct H0.
      rewrite not_in_app.
      auto.
  Qed.

  Lemma not_in_fv_Case_2 x t ts :
    x ∉ fv (Case t ts) ->
    x ∉ fv t.
  Proof.
    intros.
    unfold not.
    intros.
    rewrite fv_equation in H.
    rewrite not_in_app in H.
    destruct H.
    intuition.
  Qed.


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

  (* The propositions that we need to prove for terms and bindings *)

  Definition P_Term t := forall x t',
    x ∉ fv t ->
    subst x t' t = t.

  Definition P_Binding b := forall r x t',
    (r = Rec -> x ∉ bvb b) -> (* See Note [Assumption of subst_b and subst_br] *)
    x ∉ fvb r b ->
    subst_b x t' b = b.

  Lemma existsb_bvbs_bs x (b : binding) bs :
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
       setoid_rewrite H in H_not_in_bvb.
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
    induction xs; auto.
    intros.
    simpl in H.
    rewrite orb_false_iff in H.
    rewrite eqb_neq in H.
    apply not_in_cons.
    intuition.
  Qed.

  Lemma dec_in : ∀ (x : string) xs, {x ∈ xs} + {x ∉ xs}.
  Proof.
    intros.
    induction xs.
    - auto.
    - destruct IHxs.
      + intuition.
      + destruct (string_dec x a).
        * subst. intuition.
        * constructor 2.
          apply not_in_cons.
          intuition.
  Qed.

  Lemma subst_br_not_in_fv x t' bs t :
    x ∉ fv (Let Rec bs t) ->
    x ∉ bvbs bs -> (* See note [Assumption of subst_b and subst_br ]*)
    Util.ForallP P_Binding bs ->
    subst_br x t' bs = bs.
  Proof.
    induction bs.
    - auto.
    -
      intros H_notin_fv H_notin_bv H_bs.
      unfold subst_br.
      rewrite subst_br'_equation.
      f_equal.
      + rewrite Util.ForallP_Forall in H_bs.
        apply Forall_inv in H_bs.
        unfold P_Binding in H_bs.
        apply not_in_fv_Let_Rec_head in H_notin_fv; auto.
        apply not_in_bvbs_hd in H_notin_bv.
        eauto.

      +
        rewrite Util.ForallP_Forall in H_bs.
        inversion H_bs; subst.
        apply not_in_bvbs_cons in H_notin_bv as HH.
        rewrite <- Util.ForallP_Forall in H2.
        apply not_in_fv_Let_Rec_bs in H_notin_fv.
        * intuition.
        * intuition.
  Qed.

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
      + apply not_in_fv_Let_NonRec_hd in H_not_in_fv.
        f_equal.
        unfold P_Binding in H1.
        eapply H1; eauto.
        inversion 1.
      + (* x must be bound in bs *)
        apply existsb_not_in in H_in_bvb.
        f_equal.
          * apply not_in_fv_Let_NonRec_hd in H_not_in_fv.
            eapply H1; eauto.
          *
          destruct (existsb (eqb x) (bvbs bs)) eqn:H_ex_bvbs. 
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using not_in_fv_Let_NonRec_tl.
               eauto using existsb_bvbs_bs.
            ** assert (x ∉ fv (Let NonRec bs t)) by eauto using  not_in_fv_Let_NonRec_tl.
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
  Proof.
    induction ts;
    intros H_ts H_fv.
    - reflexivity.
    - simpl.
      inversion H_ts; subst.
      inversion H_fv; subst.
      f_equal; auto.
  Qed.

  Lemma subst_not_in_fv : forall t, P_Term t.
  Proof.
    apply term__multind with (P := P_Term) (Q := P_Binding).
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
        * rewrite <- not_in_existsb in H_eqb.
          apply not_in_fv_Let_NonRec_t in H1; eauto.

      (* Let Rec *)
      + (* x is shadowed in bs *)
        reflexivity.
      + f_equal.
        * eapply subst_br_not_in_fv with (t := t); auto.
          ** rewrite <- not_in_existsb in H_eqb. assumption.
          ** rewrite Util.ForallP_Forall in *. assumption.
        * rewrite <- not_in_existsb in H_eqb.
          eapply not_in_fv_Let_NonRec_t in H1; eauto.

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
        assert (b ≠ x) by intuition.
        unfold not; intros.
        apply H1.
        apply in_remove.
        intuition.

    - (* TypeBind *)
      unfold P_Binding.
      reflexivity.

    - (* DatatypeBind *)
      unfold P_Binding.
      reflexivity.
Qed.



End Term.
